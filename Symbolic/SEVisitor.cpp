 #include "SEVisitor.hpp"

/* ─────────────────────  Expr → SMT-LIB helper  ───────────────────── */
std::string SEVisitor::smtOf(const Expr& e)
{
    struct Local : public ASTVisitor {
        SymbolicEnv& sigma;
        std::string  smt;
        explicit Local(SymbolicEnv& s) : sigma(s) {}

        /* ---------- leaves ---------- */
        void visit(const Var& n) override
        {
            /* treat Boolean literals as genuine constants, not symbols */
            if (n.name == "true" || n.name == "false")
                smt = n.name;                       // keep as-is
            else
                smt = sigma.symFor(n.name);         // ordinary variable
        }
        void visit(const Num& n)    override { smt = std::to_string(n.value); }
        void visit(const String& n) override { smt = '"' + n.value + '"'; }

        /* ---------- function / operator ---------- */
        void visit(const FuncCall& n) override
        {
            /* spec sometimes emits true/false as zero-ary calls  */
            if ((n.name == "true" || n.name == "false") && n.args.empty()) {
                smt = n.name;
                return;
            }

            /* equals(a,b) → (= a b)  */
            if (n.name == "equals" && n.args.size() == 2) {
                Local l1(sigma); n.args[0]->accept(l1);
                Local l2(sigma); n.args[1]->accept(l2);
                smt = "(= " + l1.smt + ' ' + l2.smt + ')';
                return;
            }

            /* generic n-ary uninterpreted function      */
            smt = '(' + n.name;
            for (auto& arg : n.args) {
                Local l(sigma); arg->accept(l);
                smt += ' ' + l.smt;
            }
            smt += ')';
        }

        /* ---------- everything else is irrelevant for path constraints ---------- */
        void visit(const Set&)           override {}
        void visit(const Map&)           override {}
        void visit(const Tuple&)         override {}
        void visit(const TypeConst&)     override {}
        void visit(const FuncType&)      override {}
        void visit(const MapType&)       override {}
        void visit(const TupleType&)     override {}
        void visit(const SetType&)       override {}
        void visit(const Decl&)          override {}
        void visit(const FuncDecl&)      override {}
        void visit(const APIcall&)       override {}
        void visit(const API&)           override {}
        void visit(const Response&)      override {}
        void visit(const Init&)          override {}
        void visit(const Spec&)          override {}
        void visit(const Assign&)        override {}
        void visit(const FuncCallStmt&)  override {}
        void visit(const Program&)       override {}
    };

    Local l(sigma);
    const_cast<Expr&>(e).accept(l);          // base visitor is non-const
    return l.smt;
}

/* ─────────────────────  statement visitors  ───────────────────── */
void SEVisitor::visit(const Assign& n)
{
    std::string lhs = sigma.symFor(n.left->name);
    std::string rhs = smtOf(*n.right);

    /* avoid “(= x )” when rhs was empty (malformed AST) */
    if (!rhs.empty())
        sigma.addPredicate("(= " + lhs + ' ' + rhs + ')');
}

void SEVisitor::visit(const FuncCallStmt& n)
{
    const std::string& f = n.call->name;
    if ((f == "assume" || f == "assert") && !n.call->args.empty())
        sigma.addPredicate(smtOf(*n.call->args[0]));
}

/* ─────────────────────  trivial fall-throughs  ───────────────────── */
void SEVisitor::visit(const Var&     ) {}
void SEVisitor::visit(const FuncCall&) {}
void SEVisitor::visit(const Num&     ) {}
void SEVisitor::visit(const String&  ) {}

/* ─────────────────────  walk whole test-path program  ───────────────────── */
void SEVisitor::visit(const Program& n)
{
    for (auto& s : n.statements)
        s->accept(*this);
}