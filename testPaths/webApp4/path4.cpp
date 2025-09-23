// Path 4:
// Raise_Complaint → Assign(Plumber) → Plumber_Accept (Valid path, should return SAT)

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

    // urgency_level = input();
    {
        auto lhs = make_unique<Var>("urgency_level");
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

    // raise_complaint(complaint_description, customer_location, urgency_level, service_type);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_description"));
        a.push_back(make_unique<Var>("customer_location"));
        a.push_back(make_unique<Var>("urgency_level"));
        a.push_back(make_unique<Var>("service_type"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("raise_complaint", move(a))));
    }

    // plumber_id = input();
    {
        auto lhs = make_unique<Var>("plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // assign_plumber(complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("assign_plumber", move(a))));
    }

    // plumber_accept(complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_accept", move(a))));
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
        // Precondition: customer is authenticated (customer_token exists in sessions)
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("customer_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CustomerSessions"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(preArgs));

        // Function call to raise complaint
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_description"));
        args.push_back(make_unique<Var>("customer_location"));
        args.push_back(make_unique<Var>("urgency_level"));
        args.push_back(make_unique<Var>("service_type"));
        auto callFn = make_unique<FuncCall>("raise_complaint", move(args));

        // Postcondition: ComplaintStatus[complaint_id] == RAISED
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_RAISED"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- assign_plumber ---
    {
        vector<unique_ptr<Expr>> conj;

        // manager_token exists in ManagerSessions (manager is authenticated)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("manager_token"));
            h.push_back(make_unique<Var>("ManagerSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // complaint_id exists and is in RAISED state
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_RAISED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // plumber_id is active and has required specialization
        {
            vector<unique_ptr<Expr>> args;
            args.push_back(make_unique<Var>("plumber_id"));
            args.push_back(make_unique<Var>("service_type"));
            conj.push_back(make_unique<FuncCall>("plumber_has_specialization", move(args)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("assign_plumber", move(args));

        vector<unique_ptr<Expr>> postConj;

        // ComplaintStatus[complaint_id] == ASSIGNED
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_ASSIGNED"));
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

    // --- plumber_accept ---
    {
        vector<unique_ptr<Expr>> conj;

        // plumber_token exists in PlumberSessions (plumber is authenticated)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_token"));
            h.push_back(make_unique<Var>("PlumberSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // complaint is assigned to this plumber
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintAssignments", "complaint_id"));
            eq.push_back(make_unique<Var>("plumber_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // complaint status is ASSIGNED
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_ASSIGNED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("plumber_accept", move(args));

        vector<unique_ptr<Expr>> postConj;

        // ComplaintStatus[complaint_id] == ACCEPTED
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_ACCEPTED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // Customer gets notified about plumber details
        {
            vector<unique_ptr<Expr>> args;
            args.push_back(make_unique<Var>("complaint_id"));
            args.push_back(make_unique<Var>("plumber_id"));
            postConj.push_back(make_unique<FuncCall>("customer_notified", move(args)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- Global variable declarations ---
    vector<unique_ptr<Decl>> globals;
    
    // CustomerSessions map: token -> username
    globals.push_back(make_unique<Decl>("CustomerSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // ManagerSessions map: token -> username
    globals.push_back(make_unique<Decl>("ManagerSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // PlumberSessions map: token -> username
    globals.push_back(make_unique<Decl>("PlumberSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // ComplaintStatus map: complaint_id -> status
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // ComplaintAssignments map: complaint_id -> plumber_id
    globals.push_back(make_unique<Decl>("ComplaintAssignments", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // PlumberSpecializations map: plumber_id -> Set<ServiceType>
    globals.push_back(make_unique<Decl>("PlumberSpecializations", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("ServiceTypeSet"))));
    
    // Session tokens
    globals.push_back(make_unique<Decl>("customer_token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("manager_token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_token", make_unique<TypeConst>("string")));
    
    // Complaint and plumber IDs
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    
    // Complaint state constants
    globals.push_back(make_unique<Decl>("STATE_RAISED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_ASSIGNED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_ACCEPTED", make_unique<TypeConst>("string")));

    // --- Initialization ---
    vector<unique_ptr<Init>> inits;
    
    // Initialize CustomerSessions as empty map
    inits.push_back(make_unique<Init>("CustomerSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize ManagerSessions as empty map
    inits.push_back(make_unique<Init>("ManagerSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize PlumberSessions as empty map
    inits.push_back(make_unique<Init>("PlumberSessions", 
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