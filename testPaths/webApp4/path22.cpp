// Path 22: Quotation(spares) → Approve → Plumber_Orders(warehouse)

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

    // complaint_id = input();
    {
        auto lhs = make_unique<Var>("complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_username = input();
    {
        auto lhs = make_unique<Var>("plumber_username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // spare_items = input();
    {
        auto lhs = make_unique<Var>("spare_items");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // quotation_amount = input();
    {
        auto lhs = make_unique<Var>("quotation_amount");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // raise_quotation(complaint_id, plumber_username, spare_items, quotation_amount);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("plumber_username"));
        a.push_back(make_unique<Var>("spare_items"));
        a.push_back(make_unique<Var>("quotation_amount"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("raise_quotation", move(a))));
    }

    // customer_username = input();
    {
        auto lhs = make_unique<Var>("customer_username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // approval_complaint_id = input();
    {
        auto lhs = make_unique<Var>("approval_complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // approve_quotation(customer_username, approval_complaint_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customer_username"));
        a.push_back(make_unique<Var>("approval_complaint_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("approve_quotation", move(a))));
    }

    // order_plumber_username = input();
    {
        auto lhs = make_unique<Var>("order_plumber_username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // order_complaint_id = input();
    {
        auto lhs = make_unique<Var>("order_complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // warehouse_id = input();
    {
        auto lhs = make_unique<Var>("warehouse_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_order_warehouse(order_plumber_username, order_complaint_id, warehouse_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("order_plumber_username"));
        a.push_back(make_unique<Var>("order_complaint_id"));
        a.push_back(make_unique<Var>("warehouse_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_order_warehouse", move(a))));
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

    // --- raise_quotation ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that complaint exists and is in Under_Examination state
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_UNDER_EXAMINATION"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that plumber is assigned to this complaint
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPlumber", "complaint_id"));
            eq.push_back(make_unique<Var>("plumber_username"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_username"));
        args.push_back(make_unique<Var>("spare_items"));
        args.push_back(make_unique<Var>("quotation_amount"));
        auto callFn = make_unique<FuncCall>("raise_quotation", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_QUOTATION_RAISED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintQuotation", "complaint_id"));
            eq.push_back(make_unique<Var>("quotation_amount"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintSpares", "complaint_id"));
            eq.push_back(make_unique<Var>("spare_items"));
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
        // Check that complaint is in Quotation_Raised state
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "approval_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_QUOTATION_RAISED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that customer is the owner of this complaint
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintCustomer", "approval_complaint_id"));
            eq.push_back(make_unique<Var>("customer_username"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that spares are available in warehouse
        {
            vector<unique_ptr<Expr>> check;
            check.push_back(mapVal("ComplaintSpares", "approval_complaint_id"));
            check.push_back(make_unique<Var>("WarehouseInventory"));
            conj.push_back(make_unique<FuncCall>("spares_available", move(check)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("customer_username"));
        args.push_back(make_unique<Var>("approval_complaint_id"));
        auto callFn = make_unique<FuncCall>("approve_quotation", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "approval_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_QUOTATION_APPROVED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintApproval", "approval_complaint_id"));
            eq.push_back(make_unique<Var>("customer_username"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- plumber_order_warehouse ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that complaint is in Quotation_Approved state
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "order_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_QUOTATION_APPROVED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that plumber is assigned to this complaint
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPlumber", "order_complaint_id"));
            eq.push_back(make_unique<Var>("order_plumber_username"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that warehouse has required spares
        {
            vector<unique_ptr<Expr>> check;
            check.push_back(make_unique<Var>("warehouse_id"));
            check.push_back(mapVal("ComplaintSpares", "order_complaint_id"));
            conj.push_back(make_unique<FuncCall>("warehouse_has_spares", move(check)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("order_plumber_username"));
        args.push_back(make_unique<Var>("order_complaint_id"));
        args.push_back(make_unique<Var>("warehouse_id"));
        auto callFn = make_unique<FuncCall>("plumber_order_warehouse", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "order_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_UNDER_EXECUTION"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintWarehouseOrder", "order_complaint_id"));
            eq.push_back(make_unique<Var>("warehouse_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberOrderStatus", "order_plumber_username"));
            eq.push_back(make_unique<Var>("STATUS_ORDER_PLACED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── Globals ───
    vector<unique_ptr<Decl>> globals;

    // Map declarations for complaint and warehouse management
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintPlumber", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintCustomer", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintQuotation", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintSpares", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintApproval", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintWarehouseOrder", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberOrderStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("WarehouseInventory", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("spare_items", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("quotation_amount", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("approval_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("order_plumber_username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("order_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("warehouse_id", make_unique<TypeConst>("string")));

    // Status constants
    globals.push_back(make_unique<Decl>("STATUS_UNDER_EXAMINATION", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_QUOTATION_RAISED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_QUOTATION_APPROVED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_UNDER_EXECUTION", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ORDER_PLACED", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("ComplaintStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintPlumber", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintCustomer", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintQuotation", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintSpares", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintApproval", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintWarehouseOrder", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberOrderStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("WarehouseInventory", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();