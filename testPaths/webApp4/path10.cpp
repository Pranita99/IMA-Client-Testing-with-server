// Path 10:
// Plumber_Login → Accept_Assignment → Complete_Task (Valid path, should return SAT)

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

    // plumber_username = input();
    {
        auto lhs = make_unique<Var>("plumber_username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // plumber_password = input();
    {
        auto lhs = make_unique<Var>("plumber_password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // plumber_login(plumber_username, plumber_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("plumber_username"));
        a.push_back(make_unique<Var>("plumber_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_login", move(a))));
    }

    // assignment_id = input();
    {
        auto lhs = make_unique<Var>("assignment_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // accept_assignment(assignment_id, plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("assignment_id"));
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("accept_assignment", move(a))));
    }

    // task_completion_notes = input();
    {
        auto lhs = make_unique<Var>("task_completion_notes");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // complete_task(assignment_id, plumber_id, task_completion_notes);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("assignment_id"));
        a.push_back(make_unique<Var>("plumber_id"));
        a.push_back(make_unique<Var>("task_completion_notes"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("complete_task", move(a))));
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

    // --- plumber_login ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberCredentials", "plumber_username"));
            eq.push_back(make_unique<Var>("plumber_password"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_username"));
            h.push_back(make_unique<Var>("PlumberCredentials"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("plumber_username"));
        args.push_back(make_unique<Var>("plumber_password"));
        auto callFn = make_unique<FuncCall>("plumber_login", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberSessions", "plumber_token"));
            eq.push_back(make_unique<Var>("plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberLoginStatus", "plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_LOGGED_IN"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- accept_assignment ---
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
            eq.push_back(mapVal("PlumberLoginStatus", "plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_LOGGED_IN"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentStatus", "assignment_id"));
            eq.push_back(make_unique<Var>("STATUS_ASSIGNED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentPlumbers", "assignment_id"));
            eq.push_back(make_unique<Var>("plumber_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("assignment_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("accept_assignment", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentStatus", "assignment_id"));
            eq.push_back(make_unique<Var>("STATUS_ACCEPTED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberAssignments", "plumber_id"));
            eq.push_back(make_unique<Var>("assignment_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- complete_task ---
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
            eq.push_back(mapVal("AssignmentStatus", "assignment_id"));
            eq.push_back(make_unique<Var>("STATUS_ACCEPTED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberAssignments", "plumber_id"));
            eq.push_back(make_unique<Var>("assignment_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberLoginStatus", "plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_LOGGED_IN"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("assignment_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        args.push_back(make_unique<Var>("task_completion_notes"));
        auto callFn = make_unique<FuncCall>("complete_task", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentStatus", "assignment_id"));
            eq.push_back(make_unique<Var>("STATUS_COMPLETED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("TaskCompletionNotes", "assignment_id"));
            eq.push_back(make_unique<Var>("task_completion_notes"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CompletionTimestamps", "assignment_id"));
            eq.push_back(make_unique<Var>("current_timestamp"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- Global variable declarations ---
    vector<unique_ptr<Decl>> globals;
    
    // Authentication and session management
    globals.push_back(make_unique<Decl>("PlumberCredentials", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberLoginStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // Assignment tracking
    globals.push_back(make_unique<Decl>("AssignmentStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("AssignmentPlumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberAssignments", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // Task completion tracking
    globals.push_back(make_unique<Decl>("TaskCompletionNotes", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CompletionTimestamps", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // Input variables
    globals.push_back(make_unique<Decl>("plumber_username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_password", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("assignment_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("task_completion_notes", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("current_timestamp", make_unique<TypeConst>("string")));
    
    // Status constants
    globals.push_back(make_unique<Decl>("STATUS_LOGGED_IN", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ASSIGNED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ACCEPTED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_COMPLETED", make_unique<TypeConst>("string")));

    // --- Initialization ---
    vector<unique_ptr<Init>> inits;
    
    // Initialize authentication maps as empty
    inits.push_back(make_unique<Init>("PlumberCredentials", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("PlumberSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("PlumberLoginStatus", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize assignment tracking maps as empty
    inits.push_back(make_unique<Init>("AssignmentStatus", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("AssignmentPlumbers", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("PlumberAssignments", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize completion tracking maps as empty
    inits.push_back(make_unique<Init>("TaskCompletionNotes", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("CompletionTimestamps", 
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