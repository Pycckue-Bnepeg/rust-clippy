// TODO: как бы не забыть разработчикам добавить провайдер в `define_module`
use clippy_utils::{def_path_def_ids, get_trait_def_id};
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

#[derive(Default)]
pub struct DefineMessages {
    handlers: rustc_data_structures::fx::FxHashMap<def_id::DefId, Handler>,
    routable: Option<def_id::DefId>,
    messenger: Vec<def_id::DefId>,
    impls: rustc_data_structures::fx::FxHashMap<def_id::DefId, Span>,
    part_of_provider: Option<def_id::DefId>,
}

impl_lint_pass!(DefineMessages => [DEFINE_MESSAGES]);

impl<'tcx> LateLintPass<'tcx> for DefineMessages {
    fn check_crate(&mut self, cx: &LateContext<'tcx>) {
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

        for (_did, span) in &self.impls {
            clippy_utils::diagnostics::span_lint(
                cx,
                DEFINE_MESSAGES,
                span.clone(),
                "обработчик сообщения был имплементирован, но не указан в макросе определения модуля `define_module!`",
            );
        }
    }

    fn check_item(&mut self, _: &LateContext<'tcx>, item: &'tcx Item<'tcx>) {
        if_chain! {
            if let ItemKind::Impl(imp) = item.kind;
            if let Some(of_trait) = imp.of_trait;
            if let Some(did) = of_trait.trait_def_id();
            if self.handlers.contains_key(&did);
            then {
                let args = of_trait.path.segments.first()
                    .map(|segment| segment.args());

                if let Some(args) = args {
                    for arg in args.args {
                        match arg {
                            GenericArg::Lifetime(_) => {}
                            GenericArg::Type(ref ty) => {
                                if_chain! {
                                    if let TyKind::Path(QPath::Resolved(_, path)) = ty.kind;
                                    if let Some(did) = path.res.opt_def_id();
                                    then {
                                        self.impls.insert(did, of_trait.path.span);
                                    }
                                }

                                break;
                            }

                            GenericArg::Const(_) => {}
                            GenericArg::Infer(_) => {}
                        }
                    }
                }
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
                        self.impls.insert(p_did, *span);
                    } else {
                        self.impls.insert(msg_did, *span);
                    }
                }
            }
        }
    }
}
