use clippy_utils::{def_path_def_ids, get_trait_def_id};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::*;
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::impl_lint_pass;
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

#[derive(Debug, Clone, Copy)]
enum Handler {
    Request,
    Message,
    Notification,
    Task,
}

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
enum MacroPlace {
    Providers,
    Messages,
    Notifications,
    Tasks,
    Requests,
    EmitsNotifications,
}

#[allow(unused)]
impl MacroPlace {
    fn to_macro_ident(self) -> &'static str {
        match self {
            Self::Providers => "providers",
            Self::Messages => "messages",
            Self::Notifications => "notifications",
            Self::Tasks => "tasks",
            Self::Requests => "requests",
            Self::EmitsNotifications => "emits_notifications",
        }
    }
}

#[derive(Debug, Clone)]
enum MessageUsage {
    // emits_notifications
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
    Handler(def_id::DefId, Span, Handler),
}

impl HandleKind {
    fn def_id(&self) -> def_id::DefId {
        match self {
            Self::Handler(did, _, _) => *did,
            Self::Provider(did, _) => *did,
        }
    }

    fn span(&self) -> Span {
        match self {
            Self::Handler(_, span, _) => *span,
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
    macro_places: FxHashMap<MacroPlace, Span>,
    root_macro_call: Option<Span>,
}

impl_lint_pass!(DefineMessages => [DEFINE_MESSAGES]);

impl DefineMessages {
    #[inline]
    fn provider_impl(&self, cx: &LateContext<'_>, t: &TraitRef<'_>) -> Option<def_id::DefId> {
        if let Some(did) = t.path.res.opt_def_id()
            && let Some(p_did) = cx.tcx.opt_parent(did)
            && let DefKind::Mod = cx.tcx.def_kind(p_did)
            && let Some(did) = self.available_providers.get(&p_did)
        {
            return Some(*did);
        }

        None
    }

    #[inline]
    fn impl_kind(&self, cx: &LateContext<'_>, trait_ref: &TraitRef<'_>) -> Option<HandleKind> {
        let did = trait_ref.trait_def_id()?;

        if let Some(kind) = self.handlers.get(&did) {
            let args = trait_ref.path.segments.first().map(|segment| segment.args());

            if let Some(args) = args {
                for arg in args.args {
                    match arg {
                        GenericArg::Type(ref ty) => {
                            if let TyKind::Path(QPath::Resolved(_, path)) = ty.kind
                                && let Some(did) = path.res.opt_def_id()
                            {
                                return Some(HandleKind::Handler(did, trait_ref.path.span, *kind));
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

    #[allow(unused)]
    #[inline]
    fn suggest_span(&self, cx: &LateContext<'_>, place: MacroPlace) -> Option<(Span, bool)> {
        if let Some(span) = self.macro_places.get(&place) {
            if let Some(root) = &self.root_macro_call {
                return Some((root.with_hi(span.hi()), true));
            } else {
                return Some((*span, true));
            }
        } else {
            if let Some(root) = &self.root_macro_call {
                let snippet = clippy_utils::source::snippet(cx, *root, "..");
                let span = find_insert_span(*root, place.to_macro_ident(), &snippet)?;
                return Some((span, false));
            }
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

        // TODO: чуть прибраться в этом хламе
        for id in cx.tcx.hir().items() {
            if matches!(cx.tcx.def_kind(id.owner_id), DefKind::Impl { .. })
                && let item = cx.tcx.hir().item(id)
                && let ItemKind::Impl(Impl { items, of_trait, .. }) = &item.kind
                && let Some(of_trait) = of_trait
                && let Some(of_trait) = of_trait.trait_def_id()
                && of_trait == routable
            {
                if item.span.from_expansion() && self.root_macro_call.is_none() {
                    self.root_macro_call = clippy_utils::macros::root_macro_call(item.span).map(|c| c.span);
                }

                for item in items.iter() {
                    if let AssocItemKind::Fn { has_self: false } = item.kind
                        && (item.ident.name == sym!(router) || item.ident.name == sym!(schema))
                        && let ImplItemKind::Fn(_, body) = cx.tcx.hir().impl_item(item.id).kind
                        && let value = cx.tcx.hir().body(body).value
                        && let ExprKind::Block(Block { stmts, .. }, _) = value.kind
                    {
                        for stmt in stmts.iter() {
                            if let StmtKind::Semi(Expr {
                                kind: ExprKind::MethodCall(call_path, _, _, _),
                                ..
                            }) = stmt.kind
                                && let Some(generic) = call_path.args().args.first()
                                && let GenericArg::Type(Ty {
                                    kind: TyKind::Path(QPath::Resolved(_, path)),
                                    ..
                                }) = generic
                                && let Some(did) = path.res.opt_def_id()
                            {
                                let name = call_path.ident.name;
                                self.impls.remove(&did);

                                if name == sym!(add_provider) {
                                    self.macro_places.insert(MacroPlace::Providers, path.span);
                                }

                                if name == sym!(add_message) {
                                    self.macro_places.insert(MacroPlace::Messages, path.span);
                                }

                                if name == sym!(add_request) {
                                    self.macro_places.insert(MacroPlace::Requests, path.span);
                                }

                                if name == sym!(add_task) {
                                    self.macro_places.insert(MacroPlace::Tasks, path.span);
                                }

                                if name == sym!(add_notification) {
                                    self.macro_places.insert(MacroPlace::EmitsNotifications, path.span);
                                }

                                if name == sym!(add_handle_notification) {
                                    self.macro_places.insert(MacroPlace::Notifications, path.span);
                                }
                            }
                        }
                    }
                }
            }
        }

        for (_did, usage) in &self.impls {
            let (help, _kind) = match usage {
                MessageUsage::Notify(_, _) => (
                    "нотификация была источена, но не объявлена в `define_module!`",
                    MacroPlace::EmitsNotifications,
                ),

                MessageUsage::Handle(HandleKind::Provider(_, _)) => (
                    "провайдер был имплементирован, но не указан в `define_module!`",
                    MacroPlace::Providers,
                ),

                MessageUsage::Handle(HandleKind::Handler(_, _, kind)) => {
                    let kind = match kind {
                        Handler::Request => MacroPlace::Requests,
                        Handler::Message => MacroPlace::Messages,
                        Handler::Notification => MacroPlace::Notifications,
                        Handler::Task => MacroPlace::Tasks,
                    };

                    (
                        "обработчик сообщения был имплементирован, но не указан в `define_module!`",
                        kind,
                    )
                },
            };

            // let name = cx.tcx.def_path_str(did);

            // FIXME: разобраться по-хорошему со спанами для автоматического фикса
            // проверки на запятую отвратительные и не работают как надо
            // ...
            // if let Some((span, with_comma)) = self.suggest_span(cx, kind) {
            //     span_lint_and_then(cx, DEFINE_MESSAGES, usage.span(), help, |diag| {
            //         let source = cx.sess().source_map();
            //         let ident = clippy_utils::source::indent_of(cx, span.shrink_to_hi()).unwrap_or(0);
            //         let w = source.span_extend_to_next_char(span, ']', true);
            //         let contains_comma = clippy_utils::source::snippet(cx, w, "").contains(",");

            //         diag.span_help(span, "..добавьте сообщение в это определение..");
            //         diag.span_suggestion(
            //             span.shrink_to_hi(),
            //             "..в список",
            //             format!(
            //                 "{}{name},",
            //                 if !contains_comma {
            //                     format!(",\n{}", " ".repeat(ident))
            //                 } else {
            //                     format!("\n{}", " ".repeat(ident))
            //                 }
            //             ),
            //             Applicability::MachineApplicable,
            //         );
            //     });
            // } else {
            //     clippy_utils::diagnostics::span_lint(cx, DEFINE_MESSAGES, usage.span(), help);
            // }

            // FIXME: найти способ по надежнее ...
            // сейчас выступает в качестве проверки, является ли каким-то подобием модуля
            // иначе в `module-framework` + `providers` будет выдавать ложные ошибки
            if let Some(mac) = &self.root_macro_call {
                clippy_utils::diagnostics::span_lint_and_then(cx, DEFINE_MESSAGES, usage.span(), help, |diag| {
                    diag.span_help(*mac, "добавьте это сообщение в определение в макросе");
                });
            }
        }
    }

    fn check_item(&mut self, cx: &LateContext<'tcx>, item: &'tcx Item<'tcx>) {
        if let ItemKind::Impl(imp) = item.kind
            && let Some(of_trait) = imp.of_trait
            && let Some(kind) = self.impl_kind(cx, &of_trait)
        {
            let did = kind.def_id();
            self.impls.insert(did, MessageUsage::Handle(kind));
        }
    }

    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx rustc_hir::Expr<'tcx>) {
        if let rustc_hir::ExprKind::MethodCall(path, _, [message, ..], _) = &expr.kind
            && path.ident.name == sym!(publish)
            && let Some(did) = cx.typeck_results().type_dependent_def_id(expr.hir_id)
            && self.messenger.contains(&did)
            && let ty = cx.typeck_results().expr_ty(message)
            && let Some(msg_did) = ty.ty_adt_def().map(|adt| adt.did())
        {
            let span = message.span;
            // есть два возможных варианта:
            // - сообщение, так скажем, одинокое, то просто записываем его
            // - сообщение является частью провайдера, то тут уже следует проверить именно провайдер
            if let Some(pop) = &self.part_of_provider
                && clippy_utils::ty::implements_trait(cx, ty, *pop, &[])
                && let Some(provider) = cx.get_associated_type(ty, *pop, "Provider")
                && let Some(p_did) = provider.ty_adt_def().map(|adt| adt.did())
            {
                self.impls.insert(p_did, MessageUsage::Notify(p_did, span));
            } else {
                self.impls.insert(msg_did, MessageUsage::Notify(msg_did, span));
            }
        }
    }
}

#[allow(unused)]
fn find_insert_span(base: Span, kind: &str, text: &str) -> Option<Span> {
    let mut offset = 0;

    // отталкиваемся от первого найденного типа в макросе
    // несколько циклов потому, что именна, в теории, могут
    // пересекаться
    loop {
        if offset >= text.len() {
            break;
        }

        let idx = text[offset..].find(kind)? + kind.len();
        let mut iter = text
            .chars()
            .enumerate()
            .skip(idx)
            .skip_while(|(_, ch)| ch.is_ascii_whitespace());

        let (new_idx, ch) = iter.next()?;
        let (_, ch1) = iter.next()?;

        if ch == '=' && ch1 == '>' {
            let (idx, _) = iter.skip_while(|&(_, v)| v != '[').next()?;
            let offset = offset + idx + 1;
            let new = base.with_hi(rustc_span::BytePos(base.lo().0 + offset as u32));

            return Some(new);
        }

        offset += new_idx;
    }

    None
}