// TODO: как бы не забыть разработчикам добавить провайдер в `define_module`
use clippy_utils::{def_path_def_ids, get_trait_def_id};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::*;
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::Span;

declare_clippy_lint! {
    /// ### What it does
    ///
    /// ### Why is this bad?
    ///
    /// ### Example
    /// ```rust
    /// // example code where clippy issues a warning
    /// ```
    /// Use instead:
    /// ```rust
    /// // example code which does not raise clippy warning
    /// ```
    #[clippy::version = "1.74.0"]
    pub DEFINE_MESSAGES,
    correctness,
    "default lint description"
}

#[derive(Debug)]
enum Handler {
    Request,
    Message,
    Notification,
    Task,
}

#[derive(Debug, Clone)]
enum MessageUsage {
    Notify(def_id::DefId, Span),
    Handle(HandleKind),
}

impl MessageUsage {
    // /// сообщение, что использовано
    // fn def_id(&self) -> def_id::DefId {
    //     match self {
    //         Self::Notify(did, _) => *did,
    //         Self::Handle(kind) => kind.def_id(),
    //     }
    // }

    /// локация использования
    fn span(&self) -> Span {
        match self {
            Self::Notify(_, span) => *span,
            Self::Handle(kind) => kind.span(),
        }
    }
}

#[derive(Debug, Clone)]
enum HandleKind {
    Provider(def_id::DefId, Span),
    Handler(def_id::DefId, Span),
}

impl HandleKind {
    fn def_id(&self) -> def_id::DefId {
        match self {
            Self::Handler(did, _) => *did,
            Self::Provider(did, _) => *did,
        }
    }

    fn span(&self) -> Span {
        match self {
            Self::Handler(_, span) => *span,
            Self::Provider(_, span) => *span,
        }
    }
}

#[derive(Default)]
pub struct DefineMessages {
    handlers: FxHashMap<def_id::DefId, Handler>,
    routable: Option<def_id::DefId>,
    messenger: Vec<def_id::DefId>,
    impls: FxHashMap<def_id::DefId, MessageUsage>,
    part_of_provider: Option<def_id::DefId>,
    available_providers: FxHashMap<def_id::DefId, def_id::DefId>, // parent module -> provider struct
}

impl_lint_pass!(DefineMessages => [DEFINE_MESSAGES]);

impl DefineMessages {
    #[inline]
    fn provider_impl(&self, cx: &LateContext<'_>, t: &TraitRef<'_>) -> Option<def_id::DefId> {
        if_chain! {
            if let Some(did) = t.path.res.opt_def_id();
            if let Some(p_did) = cx.tcx.opt_parent(did);
            if let DefKind::Mod = cx.tcx.def_kind(p_did);
            if let Some(did) = self.available_providers.get(&p_did);
            then {
                return Some(*did);
            }
        }

        None
    }

    #[inline]
    fn impl_kind(&self, cx: &LateContext<'_>, trait_ref: &TraitRef<'_>) -> Option<HandleKind> {
        let did = trait_ref.trait_def_id()?;

        if self.handlers.contains_key(&did) {
            let args = trait_ref.path.segments.first().map(|segment| segment.args());

            if let Some(args) = args {
                for arg in args.args {
                    match arg {
                        GenericArg::Type(ref ty) => {
                            if_chain! {
                                if let TyKind::Path(QPath::Resolved(_, path)) = ty.kind;
                                if let Some(did) = path.res.opt_def_id();
                                then {
                                    return Some(HandleKind::Handler(did, trait_ref.path.span));
                                }
                            }

                            break;
                        },

                        _ => {},
                    }
                }
            }
        } else if let Some(pdid) = self.provider_impl(cx, trait_ref) {
            return Some(HandleKind::Provider(pdid, trait_ref.path.span));
        }

        None
    }
}

impl<'tcx> LateLintPass<'tcx> for DefineMessages {
    fn check_crate(&mut self, cx: &LateContext<'tcx>) {
        // TODO: не проверять каждый item, а просто получить все сущности, что имплементируют трейты ниже
        static REQ: &[&str] = &["module_framework", "handlers", "message_handler", "IRequestHandler"];
        static MSG: &[&str] = &["module_framework", "handlers", "message_handler", "IMessageHandler"];
        static NTY: &[&str] = &[
            "module_framework",
            "handlers",
            "message_handler",
            "INotificationHandler",
        ];

        static TSK: &[&str] = &["module_framework", "handlers", "message_handler", "ITaskHandler"];
        static ROUTABLE: &[&str] = &["module_framework", "module", "RoutableModule"];
        static MESSENGER: &[&str] = &[
            "module_framework",
            "module_messenger",
            "messenger",
            "Messenger",
            "publish",
        ];

        static PROVIDER: &[&str] = &["module_framework", "provider", "PartOfProvider"];
        static PDESC: &[&str] = &["module_framework", "provider", "ProviderDesc"];

        if let Some(req) = get_trait_def_id(cx, REQ) {
            self.handlers.insert(req, Handler::Request);
        }

        if let Some(msg) = get_trait_def_id(cx, MSG) {
            self.handlers.insert(msg, Handler::Message);
        }

        if let Some(nty) = get_trait_def_id(cx, NTY) {
            self.handlers.insert(nty, Handler::Notification);
        }

        if let Some(tsk) = get_trait_def_id(cx, TSK) {
            self.handlers.insert(tsk, Handler::Task);
        }

        self.routable = get_trait_def_id(cx, ROUTABLE);
        self.messenger = def_path_def_ids(cx, MESSENGER).collect();
        self.part_of_provider = get_trait_def_id(cx, PROVIDER);

        // поиск всех доступных провайдеров и запись их в нашу коллекцию
        if let Some(did) = get_trait_def_id(cx, PDESC) {
            self.available_providers = cx
                .tcx
                .all_impls(did)
                .filter_map(|i| {
                    let prov = cx
                        .tcx
                        .impl_trait_ref(i)
                        .and_then(|v| v.instantiate_identity().self_ty().ty_adt_def().map(|adt| adt.did()))?;

                    let parent = cx.tcx.opt_parent(i)?;
                    Some((parent, prov))
                })
                .collect();
        }
    }

    fn check_crate_post(&mut self, cx: &LateContext<'tcx>) {
        let Some(routable) = self.routable.take() else {
            return;
        };

        for id in cx.tcx.hir().items() {
            if_chain! {
                if matches!(cx.tcx.def_kind(id.owner_id), DefKind::Impl { .. });
                if let item = cx.tcx.hir().item(id);
                if let ItemKind::Impl(Impl {
                    items,
                    of_trait,
                    ..
                }) = &item.kind;
                if let Some(of_trait) = of_trait;
                if let Some(of_trait) = of_trait.trait_def_id();
                if of_trait == routable;
                then {
                    for item in items.iter() {
                        if_chain! {
                            if let AssocItemKind::Fn { has_self: false } = item.kind;
                            if item.ident.name == sym!(router) || item.ident.name == sym!(schema);
                            if let ImplItemKind::Fn(_, body) = cx.tcx.hir().impl_item(item.id).kind;
                            if let value = cx.tcx.hir().body(body).value;
                            if let ExprKind::Block(Block { stmts, .. }, _) = value.kind;
                            then {
                                for stmt in stmts.iter() {
                                    if_chain! {
                                        if let StmtKind::Semi(Expr {
                                            kind: ExprKind::MethodCall(path, _, _, _),
                                            ..
                                        }) = stmt.kind;
                                        if let Some(generic) = path.args().args.first();
                                        if let GenericArg::Type(Ty {
                                            kind: TyKind::Path(
                                                QPath::Resolved(_, path)
                                            ),
                                            ..
                                        }) = generic;
                                        if let Some(did) = path.res.opt_def_id();
                                        then {
                                            self.impls.remove(&did);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        for (_did, usage) in &self.impls {
            let help = match usage {
                MessageUsage::Notify(_, _) => "нотификация была источена, но не объявлена в `define_module!`",

                MessageUsage::Handle(HandleKind::Provider(_, _)) => {
                    "провайдер был имплементирован, но не указан в `define_module!`"
                },

                MessageUsage::Handle(HandleKind::Handler(_, _)) => {
                    "обработчик сообщения был имплементирован, но не указан в `define_module!`"
                },
            };

            clippy_utils::diagnostics::span_lint(cx, DEFINE_MESSAGES, usage.span(), help);
        }
    }

    fn check_item(&mut self, cx: &LateContext<'tcx>, item: &'tcx Item<'tcx>) {
        if_chain! {
            if let ItemKind::Impl(imp) = item.kind;
            if let Some(of_trait) = imp.of_trait;
            if let Some(kind) = self.impl_kind(cx, &of_trait);
            then {
                let did = kind.def_id();
                self.impls.insert(did, MessageUsage::Handle(kind));
            }
        }
    }

    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx rustc_hir::Expr<'tcx>) {
        if_chain! {
            if let rustc_hir::ExprKind::MethodCall(path, _, [message, ..], span) = &expr.kind;
            if path.ident.name == sym!(publish);
            if let Some(did) = cx.typeck_results().type_dependent_def_id(expr.hir_id);
            if self.messenger.contains(&did);
            if let ty = cx.typeck_results().expr_ty(message);
            if let Some(msg_did) = ty.ty_adt_def().map(|adt| adt.did());
            then {
                // есть два возможных варианта:
                // - сообщение, так скажем, одинокое, то просто записываем его
                // - сообщение является частью провайдера, то тут уже следует проверить именно провайдер
                if_chain! {
                    if let Some(pop) = &self.part_of_provider;
                    if clippy_utils::ty::implements_trait(cx, ty, *pop, &[]);
                    if let Some(provider) = cx.get_associated_type(ty, *pop, "Provider");
                    if let Some(p_did) = provider.ty_adt_def().map(|adt| adt.did());
                    then {
                        self.impls.insert(p_did, MessageUsage::Notify(p_did, *span));
                    } else {
                        self.impls.insert(msg_did, MessageUsage::Notify(msg_did, *span));
                    }
                }
            }
        }
    }
}
