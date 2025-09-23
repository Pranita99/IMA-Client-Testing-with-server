// Path 32: login(manager) → assign_complaint → assign_to_nonexistent_plumber

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

    // manager_email = input();
    {
        auto lhs = make_unique<Var>("manager_email");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // manager_password = input();
    {
        auto lhs = make_unique<Var>("manager_password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // login_manager(manager_email, manager_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("manager_email"));
        a.push_back(make_unique<Var>("manager_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_manager", move(a))));
    }

    // assign_complaint_id = input();
    {
        auto lhs = make_unique<Var>("assign_complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // assigned_plumber_id = input();
    {
        auto lhs = make_unique<Var>("assigned_plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // assign_plumber(assign_complaint_id, assigned_plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("assign_complaint_id"));
        a.push_back(make_unique<Var>("assigned_plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("assign_plumber", move(a))));
    }

    // nonexistent_complaint_id = input();
    {
        auto lhs = make_unique<Var>("nonexistent_complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // nonexistent_plumber_id = input();
    {
        auto lhs = make_unique<Var>("nonexistent_plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // assign_to_nonexistent_plumber(nonexistent_complaint_id, nonexistent_plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("nonexistent_complaint_id"));
        a.push_back(make_unique<Var>("nonexistent_plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("assign_to_nonexistent_plumber", move(a))));
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

    // --- login_manager ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that email exists in managers
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("manager_email"));
            h.push_back(make_unique<Var>("ManagerEmails"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        // Check password matches
        {
            vector<unique_ptr<Expr>> eq;
            vector<unique_ptr<Expr>> mv1;
            mv1.push_back(make_unique<Var>("ManagerPasswords"));
            vector<unique_ptr<Expr>> mv2;
            mv2.push_back(make_unique<Var>("ManagerEmails"));
            mv2.push_back(make_unique<Var>("manager_email"));
            mv1.push_back(make_unique<FuncCall>("mapped_value", move(mv2)));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(mv1)));
            eq.push_back(make_unique<Var>("manager_password"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check manager status is active
        {
            vector<unique_ptr<Expr>> eq;
            vector<unique_ptr<Expr>> mv1;
            mv1.push_back(make_unique<Var>("ManagerStatus"));
            vector<unique_ptr<Expr>> mv2;
            mv2.push_back(make_unique<Var>("ManagerEmails"));
            mv2.push_back(make_unique<Var>("manager_email"));
            mv1.push_back(make_unique<FuncCall>("mapped_value", move(mv2)));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(mv1)));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("manager_email"));
        args.push_back(make_unique<Var>("manager_password"));
        auto callFn = make_unique<FuncCall>("login_manager", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ActiveSessions", "manager_email"));
            eq.push_back(make_unique<Var>("SESSION_MANAGER"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("LoginAttempts", "manager_email"));
            eq.push_back(make_unique<Var>("LOGIN_SUCCESS"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- assign_plumber ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check complaint exists and is pending
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("assign_complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "assign_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check plumber exists and is active
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("assigned_plumber_id"));
            h.push_back(make_unique<Var>("Plumbers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberStatus", "assigned_plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that manager is logged in (session exists)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("manager_email"));
            h.push_back(make_unique<Var>("ActiveSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ActiveSessions", "manager_email"));
            eq.push_back(make_unique<Var>("SESSION_MANAGER"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("assign_complaint_id"));
        args.push_back(make_unique<Var>("assigned_plumber_id"));
        auto callFn = make_unique<FuncCall>("assign_plumber", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPlumbers", "assign_complaint_id"));
            eq.push_back(make_unique<Var>("assigned_plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "assign_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_ASSIGNED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- assign_to_nonexistent_plumber ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check complaint exists and is pending
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("nonexistent_complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "nonexistent_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that plumber does NOT exist (this is the key difference)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("nonexistent_plumber_id"));
            h.push_back(make_unique<Var>("Plumbers"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check that manager is still logged in
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("manager_email"));
            h.push_back(make_unique<Var>("ActiveSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ActiveSessions", "manager_email"));
            eq.push_back(make_unique<Var>("SESSION_MANAGER"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("nonexistent_complaint_id"));
        args.push_back(make_unique<Var>("nonexistent_plumber_id"));
        auto callFn = make_unique<FuncCall>("assign_to_nonexistent_plumber", move(args));

        vector<unique_ptr<Expr>> postConj;
        // This should result in an error state
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ErrorMessages", "nonexistent_complaint_id"));
            eq.push_back(make_unique<Var>("ERROR_PLUMBER_NOT_FOUND"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "nonexistent_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentAttempts", "nonexistent_complaint_id"));
            eq.push_back(make_unique<Var>("ASSIGNMENT_FAILED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── Globals ───
    vector<unique_ptr<Decl>> globals;

    // Map declarations for managers
    globals.push_back(make_unique<Decl>("Managers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ManagerEmails", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ManagerPasswords", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ManagerStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for complaints
    globals.push_back(make_unique<Decl>("Complaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintPlumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for plumbers
    globals.push_back(make_unique<Decl>("Plumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for sessions and authentication
    globals.push_back(make_unique<Decl>("ActiveSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("LoginAttempts", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for error handling
    globals.push_back(make_unique<Decl>("ErrorMessages", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("AssignmentAttempts", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables for manager login
    globals.push_back(make_unique<Decl>("manager_email", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("manager_password", make_unique<TypeConst>("string")));

    // Input variables for normal assignment
    globals.push_back(make_unique<Decl>("assign_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("assigned_plumber_id", make_unique<TypeConst>("string")));

    // Input variables for failed assignment
    globals.push_back(make_unique<Decl>("nonexistent_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("nonexistent_plumber_id", make_unique<TypeConst>("string")));

    // Status and session constants
    globals.push_back(make_unique<Decl>("STATUS_ACTIVE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_PENDING", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ASSIGNED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("SESSION_MANAGER", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("LOGIN_SUCCESS", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("ERROR_PLUMBER_NOT_FOUND", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("ASSIGNMENT_FAILED", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Managers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ManagerEmails", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ManagerPasswords", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ManagerStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Complaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintPlumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Plumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ActiveSessions", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("LoginAttempts", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ErrorMessages", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("AssignmentAttempts", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();