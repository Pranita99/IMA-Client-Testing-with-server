// Path8: raise_complaint → plumber_accept → quotation(spares) → customer_accept → plumber_orders(warehouse) → payment → done

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

    // Step 1: Raise Complaint
    // complaint_details = input();
    {
        auto lhs = make_unique<Var>("complaint_details");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(args))));
    }

    // complaint_id = raise_complaint(customer_id, complaint_details);
    {
        auto lhs = make_unique<Var>("complaint_id");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("customer_id"));
        args.push_back(make_unique<Var>("complaint_details"));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("raise_complaint", move(args))));
    }

    // Step 2: Plumber Accept
    // plumber_accept(complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_accept", move(args))));
    }

    // Step 3: Quotation with Spares
    // quotation_details = input();
    {
        auto lhs = make_unique<Var>("quotation_details");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(args))));
    }

    // quotation(complaint_id, quotation_details, spares_list);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("quotation_details"));
        args.push_back(make_unique<Var>("spares_list"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("quotation", move(args))));
    }

    // Step 4: Customer Accept
    // customer_accept(complaint_id, customer_id);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("customer_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("customer_accept", move(args))));
    }

    // Step 5: Plumber Orders from Warehouse
    // plumber_orders(complaint_id, warehouse_id);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("warehouse_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_orders", move(args))));
    }

    // Step 6: Payment
    // payment(complaint_id, customer_id);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("customer_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("payment", move(args))));
    }

    // Step 7: Done
    // done(complaint_id);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("done", move(args))));
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

    // ─── API 1: raise_complaint ───
    {
        vector<unique_ptr<Expr>> preConj; // no special precondition
        auto pre = make_unique<FuncCall>("and_operator", move(preConj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("customer_id"));
        args.push_back(make_unique<Var>("complaint_details"));
        auto callFn = make_unique<FuncCall>("raise_complaint", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Complaints", "complaint_id"));
            eq.push_back(make_unique<Var>("complaint_details"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 2: plumber_accept ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> in;
            in.push_back(make_unique<Var>("complaint_id"));
            in.push_back(make_unique<Var>("Complaints"));
            conj.push_back(make_unique<FuncCall>("in", move(in)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("plumber_accept", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintAssignments", "complaint_id"));
            eq.push_back(make_unique<Var>("plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 3: quotation (with spares) ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> in;
            in.push_back(make_unique<Var>("complaint_id"));
            in.push_back(make_unique<Var>("ComplaintAssignments"));
            conj.push_back(make_unique<FuncCall>("in", move(in)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("quotation_details"));
        args.push_back(make_unique<Var>("spares_list"));
        auto callFn = make_unique<FuncCall>("quotation", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Quotations", "complaint_id"));
            eq.push_back(make_unique<Var>("quotation_details"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 4: customer_accept ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> in;
            in.push_back(make_unique<Var>("complaint_id"));
            in.push_back(make_unique<Var>("Quotations"));
            conj.push_back(make_unique<FuncCall>("in", move(in)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("customer_id"));
        auto callFn = make_unique<FuncCall>("customer_accept", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_ACCEPTED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 5: plumber_orders (warehouse) ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_ACCEPTED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("warehouse_id"));
        auto callFn = make_unique<FuncCall>("plumber_orders", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Orders", "complaint_id"));
            eq.push_back(make_unique<Var>("warehouse_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 6: payment ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Orders", "complaint_id"));
            eq.push_back(make_unique<Var>("warehouse_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("customer_id"));
        auto callFn = make_unique<FuncCall>("payment", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PaymentStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PAID"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 7: done ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PaymentStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PAID"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        auto callFn = make_unique<FuncCall>("done", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_RESOLVED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── Globals ───
    vector<unique_ptr<Decl>> globals;

    globals.push_back(make_unique<Decl>("Complaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintAssignments", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("Quotations", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("QuotationStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("Orders", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PaymentStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // inputs
    globals.push_back(make_unique<Decl>("customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("warehouse_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("complaint_details", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("quotation_details", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("spares_list", make_unique<TypeConst>("string")));

    // status constants
    globals.push_back(make_unique<Decl>("STATUS_ACCEPTED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_PAID", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_RESOLVED", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Complaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintAssignments", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Quotations", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("QuotationStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Orders", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PaymentStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();