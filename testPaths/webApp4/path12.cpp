// Path 12: Plumber_Signup → Under_Training → Qualify → Accept_Assignment

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

    // plumber_signup(plumber_username, plumber_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("plumber_username"));
        a.push_back(make_unique<Var>("plumber_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_signup", move(a))));
    }

    // under_training(plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("under_training", move(a))));
    }

    // qualify(plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("qualify", move(a))));
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

    // --- plumber_signup ---
    {
        vector<unique_ptr<Expr>> preConj;
        // username not already taken
        {
            vector<unique_ptr<Expr>> notin;
            notin.push_back(make_unique<Var>("plumber_username"));
            notin.push_back(make_unique<Var>("PlumberCredentials"));
            preConj.push_back(make_unique<FuncCall>("not_in", move(notin)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(preConj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("plumber_username"));
        args.push_back(make_unique<Var>("plumber_password"));
        auto callFn = make_unique<FuncCall>("plumber_signup", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberCredentials", "plumber_username"));
            eq.push_back(make_unique<Var>("plumber_password"));
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

    // --- under_training ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberLoginStatus", "plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_LOGGED_IN"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("under_training", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberTrainingStatus", "plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_TRAINING"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- qualify ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberTrainingStatus", "plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_TRAINING"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("qualify", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberQualificationStatus", "plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_QUALIFIED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- accept_assignment (extended to require qualified) ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberQualificationStatus", "plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_QUALIFIED"));
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
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- Global variable declarations ---
    vector<unique_ptr<Decl>> globals;

    // Auth & session
    globals.push_back(make_unique<Decl>("PlumberCredentials", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberLoginStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Training & Qualification
    globals.push_back(make_unique<Decl>("PlumberTrainingStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberQualificationStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Assignments
    globals.push_back(make_unique<Decl>("AssignmentStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input vars
    globals.push_back(make_unique<Decl>("plumber_username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_password", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("assignment_id", make_unique<TypeConst>("string")));

    // Status constants
    globals.push_back(make_unique<Decl>("STATUS_LOGGED_IN", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_TRAINING", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_QUALIFIED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ACCEPTED", make_unique<TypeConst>("string")));

    // --- Initialization ---
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("PlumberCredentials", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberLoginStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberTrainingStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberQualificationStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("AssignmentStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();
