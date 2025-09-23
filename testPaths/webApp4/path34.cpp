// Path 34: signup(customer) → raise_complaint(repair) → payment_before_quotation

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

    // customer_id = input();
    {
        auto lhs = make_unique<Var>("customer_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // customer_name = input();
    {
        auto lhs = make_unique<Var>("customer_name");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // customer_email = input();
    {
        auto lhs = make_unique<Var>("customer_email");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // customer_password = input();
    {
        auto lhs = make_unique<Var>("customer_password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // customer_phone = input();
    {
        auto lhs = make_unique<Var>("customer_phone");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // customer_address = input();
    {
        auto lhs = make_unique<Var>("customer_address");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // signup_customer(customer_id, customer_name, customer_email, customer_password, customer_phone, customer_address);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customer_id"));
        a.push_back(make_unique<Var>("customer_name"));
        a.push_back(make_unique<Var>("customer_email"));
        a.push_back(make_unique<Var>("customer_password"));
        a.push_back(make_unique<Var>("customer_phone"));
        a.push_back(make_unique<Var>("customer_address"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_customer", move(a))));
    }

    // complaint_id = input();
    {
        auto lhs = make_unique<Var>("complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // repair_customer_id = input();
    {
        auto lhs = make_unique<Var>("repair_customer_id");
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

    // raise_repair_complaint(complaint_id, repair_customer_id, complaint_description, service_type, priority);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("repair_customer_id"));
        a.push_back(make_unique<Var>("complaint_description"));
        a.push_back(make_unique<Var>("service_type"));
        a.push_back(make_unique<Var>("priority"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("raise_repair_complaint", move(a))));
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

    // payment_before_quotation(payment_id, payment_complaint_id, payment_amount, payment_method);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("payment_id"));
        a.push_back(make_unique<Var>("payment_complaint_id"));
        a.push_back(make_unique<Var>("payment_amount"));
        a.push_back(make_unique<Var>("payment_method"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("payment_before_quotation", move(a))));
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

    // --- signup_customer ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that customer doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_id"));
            h.push_back(make_unique<Var>("Customers"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check that email is not already registered
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_email"));
            h.push_back(make_unique<Var>("CustomerEmails"));
            auto notInEmail = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notEmailArgs;
            notEmailArgs.push_back(move(notInEmail));
            conj.push_back(make_unique<FuncCall>("not", move(notEmailArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("customer_id"));
        args.push_back(make_unique<Var>("customer_name"));
        args.push_back(make_unique<Var>("customer_email"));
        args.push_back(make_unique<Var>("customer_password"));
        args.push_back(make_unique<Var>("customer_phone"));
        args.push_back(make_unique<Var>("customer_address"));
        auto callFn = make_unique<FuncCall>("signup_customer", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Customers", "customer_id"));
            eq.push_back(make_unique<Var>("customer_name"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerEmails", "customer_email"));
            eq.push_back(make_unique<Var>("customer_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerPasswords", "customer_id"));
            eq.push_back(make_unique<Var>("customer_password"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerPhones", "customer_id"));
            eq.push_back(make_unique<Var>("customer_phone"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerAddresses", "customer_id"));
            eq.push_back(make_unique<Var>("customer_address"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerStatus", "customer_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- raise_repair_complaint ---
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
            h.push_back(make_unique<Var>("repair_customer_id"));
            h.push_back(make_unique<Var>("Customers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerStatus", "repair_customer_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check service type is repair
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(make_unique<Var>("service_type"));
            eq.push_back(make_unique<Var>("SERVICE_TYPE_REPAIR"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("repair_customer_id"));
        args.push_back(make_unique<Var>("complaint_description"));
        args.push_back(make_unique<Var>("service_type"));
        args.push_back(make_unique<Var>("priority"));
        auto callFn = make_unique<FuncCall>("raise_repair_complaint", move(args));

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
            eq.push_back(make_unique<Var>("repair_customer_id"));
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
            eq.push_back(mapVal("ComplaintServiceType", "complaint_id"));
            eq.push_back(make_unique<Var>("SERVICE_TYPE_REPAIR"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPriority", "complaint_id"));
            eq.push_back(make_unique<Var>("priority"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- payment_before_quotation (should fail) ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check complaint exists and is pending
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("payment_complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "payment_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that payment doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("payment_id"));
            h.push_back(make_unique<Var>("Payments"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check that NO quotation exists for this complaint (key constraint)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("payment_complaint_id"));
            h.push_back(make_unique<Var>("QuotationComplaints"));
            auto notInQuote = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notQuoteArgs;
            notQuoteArgs.push_back(move(notInQuote));
            conj.push_back(make_unique<FuncCall>("not", move(notQuoteArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("payment_id"));
        args.push_back(make_unique<Var>("payment_complaint_id"));
        args.push_back(make_unique<Var>("payment_amount"));
        args.push_back(make_unique<Var>("payment_method"));
        auto callFn = make_unique<FuncCall>("payment_before_quotation", move(args));

        vector<unique_ptr<Expr>> postConj;
        // This should result in an error state - payment before quotation not allowed
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ErrorMessages", "payment_complaint_id"));
            eq.push_back(make_unique<Var>("ERROR_PAYMENT_BEFORE_QUOTATION"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "payment_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PaymentAttempts", "payment_complaint_id"));
            eq.push_back(make_unique<Var>("PAYMENT_PREMATURE"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Payment should not be created
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("payment_id"));
            h.push_back(make_unique<Var>("Payments"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            postConj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── Globals ───
    vector<unique_ptr<Decl>> globals;

    // Map declarations for customers
    globals.push_back(make_unique<Decl>("Customers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerEmails", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerPasswords", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerPhones", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerAddresses", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for complaints
    globals.push_back(make_unique<Decl>("Complaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintCustomers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintServiceType", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintPriority", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for payments and quotations
    globals.push_back(make_unique<Decl>("Payments", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("QuotationComplaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for error handling
    globals.push_back(make_unique<Decl>("ErrorMessages", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PaymentAttempts", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables for customer signup
    globals.push_back(make_unique<Decl>("customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_name", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_email", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_password", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_phone", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_address", make_unique<TypeConst>("string")));

    // Input variables for repair complaint
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("repair_customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("complaint_description", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("service_type", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("priority", make_unique<TypeConst>("string")));

    // Input variables for payment attempt
    globals.push_back(make_unique<Decl>("payment_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("payment_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("payment_amount", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("payment_method", make_unique<TypeConst>("string")));

    // Status and service type constants
    globals.push_back(make_unique<Decl>("STATUS_ACTIVE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_PENDING", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("SERVICE_TYPE_REPAIR", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("ERROR_PAYMENT_BEFORE_QUOTATION", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("PAYMENT_PREMATURE", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Customers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerEmails", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerPasswords", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerPhones", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerAddresses", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Complaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintCustomers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintServiceType", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintPriority", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Payments", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("QuotationComplaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ErrorMessages", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PaymentAttempts", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();