// Path 23: quotation(spares) → approve → plumber_orders(outside) → reimbursement

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ────────────────────────────────────────────────
// 1. Build the Client Program
// ────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // quotation_id = input();
    {
        auto lhs = make_unique<Var>("quotation_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // spare_parts_list = input();
    {
        auto lhs = make_unique<Var>("spare_parts_list");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // total_cost = input();
    {
        auto lhs = make_unique<Var>("total_cost");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_id = input();
    {
        auto lhs = make_unique<Var>("plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // create_quotation(quotation_id, spare_parts_list, total_cost, plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("quotation_id"));
        a.push_back(make_unique<Var>("spare_parts_list"));
        a.push_back(make_unique<Var>("total_cost"));
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("create_quotation", move(a))));
    }

    // approve_quotation_id = input();
    {
        auto lhs = make_unique<Var>("approve_quotation_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // approver_id = input();
    {
        auto lhs = make_unique<Var>("approver_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // approve_quotation(approve_quotation_id, approver_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("approve_quotation_id"));
        a.push_back(make_unique<Var>("approver_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("approve_quotation", move(a))));
    }

    // order_id = input();
    {
        auto lhs = make_unique<Var>("order_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // order_quotation_id = input();
    {
        auto lhs = make_unique<Var>("order_quotation_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // outside_vendor = input();
    {
        auto lhs = make_unique<Var>("outside_vendor");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // order_plumber_id = input();
    {
        auto lhs = make_unique<Var>("order_plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // create_plumber_order(order_id, order_quotation_id, outside_vendor, order_plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("order_id"));
        a.push_back(make_unique<Var>("order_quotation_id"));
        a.push_back(make_unique<Var>("outside_vendor"));
        a.push_back(make_unique<Var>("order_plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("create_plumber_order", move(a))));
    }

    // reimbursement_id = input();
    {
        auto lhs = make_unique<Var>("reimbursement_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // reimbursement_order_id = input();
    {
        auto lhs = make_unique<Var>("reimbursement_order_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // reimbursement_amount = input();
    {
        auto lhs = make_unique<Var>("reimbursement_amount");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // process_reimbursement(reimbursement_id, reimbursement_order_id, reimbursement_amount);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("reimbursement_id"));
        a.push_back(make_unique<Var>("reimbursement_order_id"));
        a.push_back(make_unique<Var>("reimbursement_amount"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("process_reimbursement", move(a))));
    }

    return Program(std::move(stmts));
}

// ────────────────────────────────────────────────
// 2. Build the API Specification
// ────────────────────────────────────────────────
static Spec buildSpec()
{
    auto mapVal = [](const string& map, const string& key){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    vector<unique_ptr<API>> blocks;

    // --- create_quotation ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that quotation doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("quotation_id"));
            h.push_back(make_unique<Var>("Quotations"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check plumber exists
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_id"));
            h.push_back(make_unique<Var>("PlumberStatus"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("quotation_id"));
        args.push_back(make_unique<Var>("spare_parts_list"));
        args.push_back(make_unique<Var>("total_cost"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("create_quotation", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Quotations", "quotation_id"));
            eq.push_back(make_unique<Var>("spare_parts_list"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationCosts", "quotation_id"));
            eq.push_back(make_unique<Var>("total_cost"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationPlumbers", "quotation_id"));
            eq.push_back(make_unique<Var>("plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationStatus", "quotation_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- approve_quotation ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationStatus", "approve_quotation_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("approve_quotation_id"));
            h.push_back(make_unique<Var>("Quotations"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("approve_quotation_id"));
        args.push_back(make_unique<Var>("approver_id"));
        auto callFn = make_unique<FuncCall>("approve_quotation", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationStatus", "approve_quotation_id"));
            eq.push_back(make_unique<Var>("STATUS_APPROVED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationApprovers", "approve_quotation_id"));
            eq.push_back(make_unique<Var>("approver_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- create_plumber_order ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationStatus", "order_quotation_id"));
            eq.push_back(make_unique<Var>("STATUS_APPROVED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("order_id"));
            h.push_back(make_unique<Var>("PlumberOrders"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("order_id"));
        args.push_back(make_unique<Var>("order_quotation_id"));
        args.push_back(make_unique<Var>("outside_vendor"));
        args.push_back(make_unique<Var>("order_plumber_id"));
        auto callFn = make_unique<FuncCall>("create_plumber_order", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberOrders", "order_id"));
            eq.push_back(make_unique<Var>("order_quotation_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("OrderVendors", "order_id"));
            eq.push_back(make_unique<Var>("outside_vendor"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("OrderPlumbers", "order_id"));
            eq.push_back(make_unique<Var>("order_plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("OrderStatus", "order_id"));
            eq.push_back(make_unique<Var>("STATUS_ORDERED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- process_reimbursement ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("OrderStatus", "reimbursement_order_id"));
            eq.push_back(make_unique<Var>("STATUS_ORDERED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("reimbursement_order_id"));
            h.push_back(make_unique<Var>("PlumberOrders"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("reimbursement_id"));
            h.push_back(make_unique<Var>("Reimbursements"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("reimbursement_id"));
        args.push_back(make_unique<Var>("reimbursement_order_id"));
        args.push_back(make_unique<Var>("reimbursement_amount"));
        auto callFn = make_unique<FuncCall>("process_reimbursement", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Reimbursements", "reimbursement_id"));
            eq.push_back(make_unique<Var>("reimbursement_order_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ReimbursementAmounts", "reimbursement_id"));
            eq.push_back(make_unique<Var>("reimbursement_amount"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ReimbursementStatus", "reimbursement_id"));
            eq.push_back(make_unique<Var>("STATUS_PROCESSED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── Globals ───
    vector<unique_ptr<Decl>> globals;

    // Map declarations for quotations
    globals.push_back(make_unique<Decl>("Quotations", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("QuotationCosts", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("QuotationPlumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("QuotationStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("QuotationApprovers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for orders
    globals.push_back(make_unique<Decl>("PlumberOrders", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("OrderVendors", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("OrderPlumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("OrderStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for reimbursements
    globals.push_back(make_unique<Decl>("Reimbursements", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ReimbursementAmounts", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ReimbursementStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Existing plumber management maps (referenced)
    globals.push_back(make_unique<Decl>("PlumberStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables for quotation
    globals.push_back(make_unique<Decl>("quotation_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("spare_parts_list", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("total_cost", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_id", make_unique<TypeConst>("string")));

    // Input variables for approval
    globals.push_back(make_unique<Decl>("approve_quotation_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("approver_id", make_unique<TypeConst>("string")));

    // Input variables for order
    globals.push_back(make_unique<Decl>("order_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("order_quotation_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("outside_vendor", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("order_plumber_id", make_unique<TypeConst>("string")));

    // Input variables for reimbursement
    globals.push_back(make_unique<Decl>("reimbursement_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("reimbursement_order_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("reimbursement_amount", make_unique<TypeConst>("string")));

    // Status constants
    globals.push_back(make_unique<Decl>("STATUS_PENDING", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_APPROVED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ORDERED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_PROCESSED", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Quotations", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("QuotationCosts", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("QuotationPlumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("QuotationStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("QuotationApprovers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberOrders", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("OrderVendors", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("OrderPlumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("OrderStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Reimbursements", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ReimbursementAmounts", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ReimbursementStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();