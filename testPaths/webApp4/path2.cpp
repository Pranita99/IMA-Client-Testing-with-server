// Path 2:
// Signup(Manager) → Login → Assign_Complaint (Valid path, should return SAT)

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

    // manager_username = input();
    {
        auto lhs = make_unique<Var>("manager_username");
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

    // manager_email = input();
    {
        auto lhs = make_unique<Var>("manager_email");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // manager_region = input();
    {
        auto lhs = make_unique<Var>("manager_region");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // signup_manager(manager_username, manager_password, manager_email, manager_region);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("manager_username"));
        a.push_back(make_unique<Var>("manager_password"));
        a.push_back(make_unique<Var>("manager_email"));
        a.push_back(make_unique<Var>("manager_region"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_manager", move(a))));
    }

    // login_manager(manager_username, manager_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("manager_username"));
        a.push_back(make_unique<Var>("manager_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_manager", move(a))));
    }

    // complaint_id = input();
    {
        auto lhs = make_unique<Var>("complaint_id");
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

    // assign_complaint(complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("assign_complaint", move(a))));
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

    // --- signup_manager ---
    {
        // Precondition: manager_username not in domain of ServiceManagers
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("manager_username"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ServiceManagers"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(preArgs));

        // Function call with manager details
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("manager_username"));
        args.push_back(make_unique<Var>("manager_password"));
        args.push_back(make_unique<Var>("manager_email"));
        args.push_back(make_unique<Var>("manager_region"));
        auto callFn = make_unique<FuncCall>("signup_manager", move(args));

        // Postcondition: ServiceManagers[manager_username] == manager_profile
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ServiceManagers", "manager_username"));
        eq.push_back(make_unique<Var>("manager_profile"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- login_manager ---
    {
        vector<unique_ptr<Expr>> conj;

        // ServiceManagers[manager_username] contains manager_password
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ServiceManagers", "manager_username"));
            eq.push_back(make_unique<Var>("manager_password"));
            conj.push_back(make_unique<FuncCall>("contains_password", move(eq)));
        }

        // manager_token not in domain of ManagerSessions
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("ManagerSessions"));
            h.push_back(make_unique<Var>("manager_token"));
            conj.push_back(make_unique<FuncCall>("not_in", move(h)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("manager_username"));
        args.push_back(make_unique<Var>("manager_password"));
        auto callFn = make_unique<FuncCall>("login_manager", move(args));

        // Postcondition: ManagerSessions[manager_token] == manager_username
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ManagerSessions", "manager_token"));
        eq.push_back(make_unique<Var>("manager_username"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- assign_complaint ---
    {
        vector<unique_ptr<Expr>> conj;

        // manager_token exists in ManagerSessions (manager is authenticated)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("manager_token"));
            h.push_back(make_unique<Var>("ManagerSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // complaint_id exists in Complaints and is in "Raised" state
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("RAISED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // plumber_id exists in ActivePlumbers
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_id"));
            h.push_back(make_unique<Var>("ActivePlumbers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("assign_complaint", move(args));

        vector<unique_ptr<Expr>> postConj;

        // ComplaintStatus[complaint_id] == ASSIGNED
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("ASSIGNED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // ComplaintAssignments[complaint_id] == plumber_id
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintAssignments", "complaint_id"));
            eq.push_back(make_unique<Var>("plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- Global variable declarations ---
    vector<unique_ptr<Decl>> globals;
    
    // ServiceManagers map: username -> manager profile
    globals.push_back(make_unique<Decl>("ServiceManagers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("ManagerProfile"))));
    
    // ManagerSessions map: token -> username
    globals.push_back(make_unique<Decl>("ManagerSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // ComplaintStatus map: complaint_id -> status
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // ComplaintAssignments map: complaint_id -> plumber_id
    globals.push_back(make_unique<Decl>("ComplaintAssignments", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // ActivePlumbers set: plumber_ids that are available for assignment
    globals.push_back(make_unique<Decl>("ActivePlumbers", make_unique<TypeConst>("Set")));
    
    // Manager session token
    globals.push_back(make_unique<Decl>("manager_token", make_unique<TypeConst>("string")));
    
    // Manager profile containing all manager details
    globals.push_back(make_unique<Decl>("manager_profile", make_unique<TypeConst>("ManagerProfile")));
    
    // Complaint status constants
    globals.push_back(make_unique<Decl>("RAISED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("ASSIGNED", make_unique<TypeConst>("string")));

    // --- Initialization ---
    vector<unique_ptr<Init>> inits;
    
    // Initialize ServiceManagers as empty map
    inits.push_back(make_unique<Init>("ServiceManagers", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize ManagerSessions as empty map
    inits.push_back(make_unique<Init>("ManagerSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize ComplaintStatus as empty map
    inits.push_back(make_unique<Init>("ComplaintStatus", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize ComplaintAssignments as empty map
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