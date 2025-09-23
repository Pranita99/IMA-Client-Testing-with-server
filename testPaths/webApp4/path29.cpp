// Path 29: raise_complaint → payment_without_task_completion

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

    // customer_id = input();
    {
        auto lhs = make_unique<Var>("customer_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // complaint_description = input();
    {
        auto lhs = make_unique<Var>("complaint_description");
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

    // priority = input();
    {
        auto lhs = make_unique<Var>("priority");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // raise_complaint(complaint_id, customer_id, complaint_description, service_type, priority);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("customer_id"));
        a.push_back(make_unique<Var>("complaint_description"));
        a.push_back(make_unique<Var>("service_type"));
        a.push_back(make_unique<Var>("priority"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("raise_complaint", move(a))));
    }

    // payment_id = input();
    {
        auto lhs = make_unique<Var>("payment_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // payment_complaint_id = input();
    {
        auto lhs = make_unique<Var>("payment_complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // payment_customer_id = input();
    {
        auto lhs = make_unique<Var>("payment_customer_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // payment_amount = input();
    {
        auto lhs = make_unique<Var>("payment_amount");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // payment_method = input();
    {
        auto lhs = make_unique<Var>("payment_method");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // payment_type = input();
    {
        auto lhs = make_unique<Var>("payment_type");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // make_advance_payment(payment_id, payment_complaint_id, payment_customer_id, payment_amount, payment_method, payment_type);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("payment_id"));
        a.push_back(make_unique<Var>("payment_complaint_id"));
        a.push_back(make_unique<Var>("payment_customer_id"));
        a.push_back(make_unique<Var>("payment_amount"));
        a.push_back(make_unique<Var>("payment_method"));
        a.push_back(make_unique<Var>("payment_type"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("make_advance_payment", move(a))));
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

    // --- raise_complaint ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that complaint doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check customer exists and is active
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_id"));
            h.push_back(make_unique<Var>("Customers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerStatus", "customer_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("customer_id"));
        args.push_back(make_unique<Var>("complaint_description"));
        args.push_back(make_unique<Var>("service_type"));
        args.push_back(make_unique<Var>("priority"));
        auto callFn = make_unique<FuncCall>("raise_complaint", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Complaints", "complaint_id"));
            eq.push_back(make_unique<Var>("complaint_description"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintCustomers", "complaint_id"));
            eq.push_back(make_unique<Var>("customer_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPriority", "complaint_id"));
            eq.push_back(make_unique<Var>("priority"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintServiceTypes", "complaint_id"));
            eq.push_back(make_unique<Var>("service_type"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- make_advance_payment (allows payment before task completion) ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check complaint exists
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("payment_complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        // Check customer matches complaint
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintCustomers", "payment_complaint_id"));
            eq.push_back(make_unique<Var>("payment_customer_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check customer is active
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerStatus", "payment_customer_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check payment doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("payment_id"));
            h.push_back(make_unique<Var>("Payments"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check payment type is valid for advance payment
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(make_unique<Var>("payment_type"));
            eq.push_back(make_unique<Var>("TYPE_ADVANCE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Allow payment even when complaint is still pending (not completed)
        // This is what makes it different from regular payment - no completion required
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("payment_id"));
        args.push_back(make_unique<Var>("payment_complaint_id"));
        args.push_back(make_unique<Var>("payment_customer_id"));
        args.push_back(make_unique<Var>("payment_amount"));
        args.push_back(make_unique<Var>("payment_method"));
        args.push_back(make_unique<Var>("payment_type"));
        auto callFn = make_unique<FuncCall>("make_advance_payment", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Payments", "payment_id"));
            eq.push_back(make_unique<Var>("payment_amount"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PaymentComplaints", "payment_id"));
            eq.push_back(make_unique<Var>("payment_complaint_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PaymentCustomers", "payment_id"));
            eq.push_back(make_unique<Var>("payment_customer_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PaymentMethods", "payment_id"));
            eq.push_back(make_unique<Var>("payment_method"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PaymentTypes", "payment_id"));
            eq.push_back(make_unique<Var>("payment_type"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PaymentStatus", "payment_id"));
            eq.push_back(make_unique<Var>("STATUS_PAYMENT_COMPLETED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPaymentStatus", "payment_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_ADVANCE_PAID"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── Globals ───
    vector<unique_ptr<Decl>> globals;

    // Map declarations for complaints
    globals.push_back(make_unique<Decl>("Complaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintCustomers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintPriority", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintServiceTypes", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintPaymentStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for payments
    globals.push_back(make_unique<Decl>("Payments", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PaymentComplaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PaymentCustomers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PaymentMethods", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PaymentTypes", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PaymentStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for customers
    globals.push_back(make_unique<Decl>("Customers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables for complaint
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("complaint_description", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("service_type", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("priority", make_unique<TypeConst>("string")));

    // Input variables for payment
    globals.push_back(make_unique<Decl>("payment_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("payment_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("payment_customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("payment_amount", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("payment_method", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("payment_type", make_unique<TypeConst>("string")));

    // Status constants
    globals.push_back(make_unique<Decl>("STATUS_PENDING", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ACTIVE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_PAYMENT_COMPLETED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ADVANCE_PAID", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("TYPE_ADVANCE", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Complaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintCustomers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintPriority", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintServiceTypes", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintPaymentStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Payments", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PaymentComplaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PaymentCustomers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PaymentMethods", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PaymentTypes", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PaymentStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Customers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();