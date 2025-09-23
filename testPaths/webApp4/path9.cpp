// Path 9:
// Raise_Complaint → Reassign(Manager) → Plumber_Accept → Done (Valid path, should return SAT)

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ────────────────────────────────────────────────
// 1. Build the Client Program (imperative path)
// ────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // complaint_description = input();
    {
        auto lhs = make_unique<Var>("complaint_description");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // customer_location = input();
    {
        auto lhs = make_unique<Var>("customer_location");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // service_type = input();
    {
        auto lhs = make_unique<Var>("service_type");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // raise_complaint(complaint_description, customer_location, service_type);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_description"));
        a.push_back(make_unique<Var>("customer_location"));
        a.push_back(make_unique<Var>("service_type"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("raise_complaint", move(a))));
    }

    // new_plumber_id = input();
    {
        auto lhs = make_unique<Var>("new_plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // reassign_plumber(complaint_id, new_plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("new_plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("reassign_plumber", move(a))));
    }

    // plumber_accept(complaint_id, new_plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("new_plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_accept", move(a))));
    }

    // mark_done(complaint_id, new_plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("new_plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("mark_done", move(a))));
    }

    return Program(std::move(stmts));
}

// ────────────────────────────────────────────────
// 2. Build the API specification
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

    // --- raise_complaint ---
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("customer_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CustomerSessions"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_description"));
        args.push_back(make_unique<Var>("customer_location"));
        args.push_back(make_unique<Var>("service_type"));
        auto callFn = make_unique<FuncCall>("raise_complaint", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_RAISED"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- reassign_plumber ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("manager_token"));
            h.push_back(make_unique<Var>("ManagerSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_RAISED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("new_plumber_id"));
        auto callFn = make_unique<FuncCall>("reassign_plumber", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_ASSIGNED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintAssignments", "complaint_id"));
            eq.push_back(make_unique<Var>("new_plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- plumber_accept ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_token"));
            h.push_back(make_unique<Var>("PlumberSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_ASSIGNED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintAssignments", "complaint_id"));
            eq.push_back(make_unique<Var>("new_plumber_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("new_plumber_id"));
        auto callFn = make_unique<FuncCall>("plumber_accept", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_ACCEPTED"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- mark_done ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_token"));
            h.push_back(make_unique<Var>("PlumberSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_ACCEPTED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintAssignments", "complaint_id"));
            eq.push_back(make_unique<Var>("new_plumber_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("new_plumber_id"));
        auto callFn = make_unique<FuncCall>("mark_done", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_COMPLETED"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- Global variable declarations ---
    vector<unique_ptr<Decl>> globals;
    
    // User session maps
    globals.push_back(make_unique<Decl>("CustomerSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ManagerSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // Complaint tracking maps
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintAssignments", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // Session tokens
    globals.push_back(make_unique<Decl>("customer_token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("manager_token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_token", make_unique<TypeConst>("string")));
    
    // Complaint ID and plumber ID
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("new_plumber_id", make_unique<TypeConst>("string")));
    
    // Complaint state constants
    globals.push_back(make_unique<Decl>("STATE_RAISED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_ASSIGNED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_ACCEPTED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_COMPLETED", make_unique<TypeConst>("string")));

    // --- Initialization ---
    vector<unique_ptr<Init>> inits;
    
    // Initialize all session maps as empty
    inits.push_back(make_unique<Init>("CustomerSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("ManagerSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("PlumberSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize complaint tracking maps as empty
    inits.push_back(make_unique<Init>("ComplaintStatus", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("ComplaintAssignments", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();