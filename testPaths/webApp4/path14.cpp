// Path 14: raise_complaint → assign(plumber) → plumber_accept → visit → quotation → customer_ask_more_options → reassign → plumber_accept → done

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

    // Step 2: Assign Plumber
    // assign(complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("assign", move(args))));
    }

    // Step 3: Plumber Accept (First Time)
    // plumber_accept(complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_accept", move(args))));
    }

    // Step 4: Visit
    // visit_details = input();
    {
        auto lhs = make_unique<Var>("visit_details");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(args))));
    }

    // visit(complaint_id, plumber_id, visit_details);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        args.push_back(make_unique<Var>("visit_details"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("visit", move(args))));
    }

    // Step 5: Quotation
    // quotation_details = input();
    {
        auto lhs = make_unique<Var>("quotation_details");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(args))));
    }

    // quotation(complaint_id, plumber_id, quotation_details);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        args.push_back(make_unique<Var>("quotation_details"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("quotation", move(args))));
    }

    // Step 6: Customer Ask More Options
    // more_options_request = input();
    {
        auto lhs = make_unique<Var>("more_options_request");
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(args))));
    }

    // customer_ask_more_options(complaint_id, customer_id, more_options_request);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("customer_id"));
        args.push_back(make_unique<Var>("more_options_request"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("customer_ask_more_options", move(args))));
    }

    // Step 7: Reassign (New Plumber)
    // reassign(complaint_id, new_plumber_id);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("new_plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("reassign", move(args))));
    }

    // Step 8: Plumber Accept (Second Time - New Plumber)
    // plumber_accept(complaint_id, new_plumber_id);
    {
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("new_plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_accept", move(args))));
    }

    // Step 9: Done
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
        vector<unique_ptr<Expr>> preConj;
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

    // ─── API 2: assign ───
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
        auto callFn = make_unique<FuncCall>("assign", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignedPlumbers", "complaint_id"));
            eq.push_back(make_unique<Var>("plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 3: plumber_accept ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignedPlumbers", "complaint_id"));
            eq.push_back(make_unique<Var>("plumber_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("plumber_accept", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AcceptedComplaints", "complaint_id"));
            eq.push_back(make_unique<Var>("plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 4: visit ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AcceptedComplaints", "complaint_id"));
            eq.push_back(make_unique<Var>("plumber_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        args.push_back(make_unique<Var>("visit_details"));
        auto callFn = make_unique<FuncCall>("visit", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Visits", "complaint_id"));
            eq.push_back(make_unique<Var>("visit_details"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 5: quotation ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> in;
            in.push_back(make_unique<Var>("complaint_id"));
            in.push_back(make_unique<Var>("Visits"));
            conj.push_back(make_unique<FuncCall>("in", move(in)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        args.push_back(make_unique<Var>("quotation_details"));
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

    // ─── API 6: customer_ask_more_options ───
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
        args.push_back(make_unique<Var>("more_options_request"));
        auto callFn = make_unique<FuncCall>("customer_ask_more_options", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("MoreOptionsRequests", "complaint_id"));
            eq.push_back(make_unique<Var>("more_options_request"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 7: reassign ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> in;
            in.push_back(make_unique<Var>("complaint_id"));
            in.push_back(make_unique<Var>("MoreOptionsRequests"));
            conj.push_back(make_unique<FuncCall>("in", move(in)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("new_plumber_id"));
        auto callFn = make_unique<FuncCall>("reassign", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignedPlumbers", "complaint_id"));
            eq.push_back(make_unique<Var>("new_plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));
        Response resp(HTTPResponseCode::OK_200, post->clone());

        auto apicall = make_unique<APIcall>(move(callFn), Response(HTTPResponseCode::OK_200, post->clone()));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── API 8: done ───
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> in;
            in.push_back(make_unique<Var>("complaint_id"));
            in.push_back(make_unique<Var>("AcceptedComplaints"));
            conj.push_back(make_unique<FuncCall>("in", move(in)));
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
    globals.push_back(make_unique<Decl>("AssignedPlumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("AcceptedComplaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("Visits", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("Quotations", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("MoreOptionsRequests", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // inputs
    globals.push_back(make_unique<Decl>("customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("new_plumber_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("complaint_details", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("visit_details", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("quotation_details", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("more_options_request", make_unique<TypeConst>("string")));

    // status constants
    globals.push_back(make_unique<Decl>("STATUS_RESOLVED", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Complaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("AssignedPlumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("AcceptedComplaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Visits", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Quotations", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("MoreOptionsRequests", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
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