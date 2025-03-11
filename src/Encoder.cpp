#include "Encoder.hpp"

Encoder::Encoder(const std::vector<Item> &items) : items(items) {}

// Declares the problem to be unsat
void Encoder::declare_unsat(){
    std::cout << "UNSAT" << std::endl;
    unsat = true;
}

// Passes through the list of items which constitute the problem
// and calls the appropriate encoder function
std::vector<std::vector<Literal*>> Encoder::encode_to_cnf() {

    for (auto& item : items) {
            if(unsat)
                break;
            else if(holds_alternative<Parameter*>(item))
                encode_parameter(*get<Parameter*>(item), cnf_clauses);
            else if(holds_alternative<Variable*>(item))
                encode_variable(*get<Variable*>(item), cnf_clauses);
            else if(holds_alternative<Constraint*>(item))
                encode_constraint(*get<Constraint*>(item), cnf_clauses);
            else{
                std::cerr << "Unknown item type in encoder" << std::endl;
                break;
            }
    }

    return cnf_clauses;
}

// Converts the encoded problem to the DIMACS format
// and writes the output to the file named fileName
void Encoder::write_to_file(std::string fileName){

    std::ofstream file(fileName);

    if (!file.is_open()){
        std::cerr << "Cannot open file" << std::endl;
        return;
    }    

    file << "                                                   " << std::endl;
    for(const auto& c : cnf_clauses) {
        for(const auto &l : c){

            tuple<LiteralType, int, int> type_and_id = {l->type, l->id, l->val};
            if(literal_to_num.find(type_and_id) == literal_to_num.end()){
                literal_to_num[type_and_id] = next_dimacs_num++;
                if(l->type == LiteralType::ORDER || l->type == LiteralType::BOOL_VARIABLE)
                    num_to_literal[next_dimacs_num-1] = l;
            } 

            file << (l->pol ? literal_to_num[type_and_id] : -literal_to_num[type_and_id]) << " ";
        }
        file << 0 << std::endl;
    }    

    file.seekp(0, std::ios::beg);
    file << "p cnf " << next_dimacs_num - 1  << " " << cnf_clauses.size() << std::endl;

}

// Runs the MiniSat solver by executing the appropriate system call.
// The input in DIMACS format should be in the inputFile, and the output is
// written to the outputFile
void Encoder::run_minisat(const std::string& inputFile, const std::string& outputFile) {

    std::string command = "minisat " + inputFile + " " + outputFile +  "> /dev/null 2>&1";

    std::system(command.c_str());
}

// Reads the MiniSat solver output, converts it to a human readable format
// and writes the output to std::cout
void Encoder::read_minisat_output(const std::string& outputFile) {
    std::ifstream output(outputFile);
    if (!output.is_open()) {
        std::cerr << "Cannot open file" << std::endl;
        return;
    }

    std::string sat;
    output >> sat;
    if(sat == "UNSAT"){
        declare_unsat();
        return;
    }

    std::cout << "SAT" << std::endl;

    int curr_lit_num;
    while (output >> curr_lit_num) {

        bool sign = false;
        if(curr_lit_num < 0){
            sign = true;
            curr_lit_num = -curr_lit_num;
        }

        if(num_to_literal.find(curr_lit_num) == num_to_literal.end())
            continue;

        auto l = num_to_literal[curr_lit_num];

        if(id_map.find(l->id) == id_map.end())
            continue;

        Variable* curr_var = id_map[l->id];
        BasicVar* curr_basic_var = get<BasicVar*>(*curr_var);
        BasicVarType* curr_basic_var_type = curr_basic_var->type;

        if(holds_alternative<IntRangeVarType*>(*curr_basic_var_type)){
            IntRangeVarType* c = get<IntRangeVarType*>(*curr_basic_var_type);
            int val = l->val;
            if(!sign){
                if(c->right > val)
                    c->right = val;
            } else {
                if(c->left < val + 1)
                    c->left = val + 1;
            }

            if(c->left == c->right){
                std::cout << *curr_basic_var->name << " = " << c->left << std::endl;
                id_map.erase(l->id);
            } 
        } else if(holds_alternative<BasicParType>(*curr_basic_var_type)){
            if(get<BasicParType>(*curr_basic_var_type) == BasicParType::BOOL){
                if(!sign)
                    std::cout << *curr_basic_var->name << " = true" << std::endl; 
                else
                    std::cout << *curr_basic_var->name << " = false" << std::endl;
                id_map.erase(l->id);                    
            }
        }

    }

    output.close();
}

// Encodes a parameter of the model 
void Encoder::encode_parameter(Parameter& param, std::vector<std::vector<Literal*>>& cnf_clauses) {

    parameter_map[*param.name] = &param;

}

// Encodes a variable based on it's type.
void Encoder::encode_variable(Variable& var, std::vector<std::vector<Literal*>>& cnf_clauses) {
    int new_var_id = next_var_id++;

    if (holds_alternative<BasicVar*>(var)) {
        BasicVar* basic_var = get<BasicVar*>(var);
        variable_map[*basic_var->name] = &var; 
        basic_var->id = new_var_id;

        id_map[new_var_id] = variable_map[*basic_var->name];
        
        if(holds_alternative<IntRangeVarType*>(*basic_var->type)){
            IntRangeVarType* t = get<IntRangeVarType*>(*basic_var->type);


            int left = t->left;
            int right = t->right;

            std::vector<Literal*> clause1, clause2, curr_clause;
            clause1 = {new Literal(LiteralType::ORDER, new_var_id, false, left - 1)};
            clause2 = {new Literal(LiteralType::ORDER, new_var_id, true, right)};

            cnf_clauses.push_back(clause1);
            cnf_clauses.push_back(clause2);
            for(int i = left; i <= right; i++){
                curr_clause.push_back(new Literal(LiteralType::ORDER, new_var_id, false, i - 1));
                curr_clause.push_back(new Literal(LiteralType::ORDER, new_var_id, true, i));
                cnf_clauses.push_back(curr_clause);
                curr_clause.clear();
            }
        } else if(holds_alternative<BasicParType>(*basic_var->type)){
            if(get<BasicParType>(*basic_var->type) == BasicParType::BOOL){
                std::vector<Literal*> clause;
                clause.push_back(new Literal(LiteralType::BOOL_VARIABLE, basic_var->id, true, 0));
                clause.push_back(new Literal(LiteralType::BOOL_VARIABLE, basic_var->id, false, 0));  
                cnf_clauses.push_back(clause);
            }
        }
    } else {
        ArrayVar* array_var = get<ArrayVar*>(var);
        variable_map[*array_var->name] = &var;  
    
    }
}

// Encodes a helper variable for substitutions
BasicVar* Encoder::encode_int_range_helper_variable(const int left, const int right, std::vector<std::vector<Literal*>>& cnf_clauses) {

    int sub_id = next_var_id++;
    auto var_type = new IntRangeVarType(left, right);
    string* name = new string(format("sub_{}", sub_id));
    auto int_range_var = new BasicVar(new BasicVarType(var_type), name, true);
    int_range_var->id = sub_id;

    // variable_map[*int_range_var->name] = new Variable(int_range_var);
    // id_map[sub_id] = variable_map[*int_range_var->name];


    std::vector<Literal*> clause1, clause2, curr_clause;
    clause1 = {new Literal(LiteralType::ORDER, sub_id, false, left - 1)};
    clause2 = {new Literal(LiteralType::ORDER, sub_id, true, right)};

    cnf_clauses.push_back(clause1);
    cnf_clauses.push_back(clause2);
    for(int i = left; i <= right; i++){
        curr_clause.push_back(new Literal(LiteralType::ORDER, sub_id, false, i - 1));
        curr_clause.push_back(new Literal(LiteralType::ORDER, sub_id, true, i));

        cnf_clauses.push_back(curr_clause);
        curr_clause.clear();
    }    

    return int_range_var;
}

// Gets the left border of an IntRange variable
int get_left(const BasicVar* var){
    return get<IntRangeVarType*>(*var->type)->left;
}

// Gets the right border of an IntRange variable
int get_right(const BasicVar* var){
    return get<IntRangeVarType*>(*var->type)->right;
}

// Makes a connection between a direct and order encoding of a variable.
// The variable is supposed to already be encoded using the order encoding
void Encoder::encode_direct(const BasicVar& var, std::vector<std::vector<Literal*>>& cnf_clauses){
    
    int left = get_left(&var);
    int right = get_right(&var);

    for(int i = left; i <= right; i++){
        Literal* p = new Literal(LiteralType::DIRECT, var.id, true, i);
        Literal* q = new Literal(LiteralType::ORDER, var.id, true, i);
        Literal* r = new Literal(LiteralType::ORDER, var.id, true, i-1);
        Literal* not_p = new Literal(LiteralType::DIRECT, var.id, false, i);
        Literal* not_q = new Literal(LiteralType::ORDER, var.id, false, i);
        Literal* not_r = new Literal(LiteralType::ORDER, var.id, false, i-1);

        vector<Literal*> new_clause1 = {not_p, q};
        vector<Literal*> new_clause2 = {not_p, not_r};
        vector<Literal*> new_clause3 = {p, not_q, r};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);
        cnf_clauses.push_back(new_clause3);
    }

}

// Gets a variable argument at index ind from constraint constr
BasicVar* Encoder::get_var(Constraint& constr, int ind){
    auto tmp1 = (*constr.args)[ind];
    auto tmp2 = get<BasicExpr*>(*tmp1);
    auto tmp3 = get<string*>(*tmp2);
    return get<BasicVar*>(*variable_map[*tmp3]);

}

// Gets an array argument at index ind from constraint constr
ArrayLiteral* Encoder::get_array(Constraint& constr, int ind){
    auto tmp1 = (*constr.args)[ind];
    if(holds_alternative<BasicExpr*>(*tmp1)){
        auto tmp2 = get<BasicExpr*>(*tmp1);
        auto tmp3 = get<string*>(*tmp2);
        if(variable_map.find(*tmp3) != variable_map.end()){
            auto tmp4 = get<ArrayVar*>(*variable_map[*tmp3]);
            return tmp4->value;
        } else if(parameter_map.find(*tmp3) != parameter_map.end()){
            auto tmp4 = get<ParArrayLiteral*>(*parameter_map[*tmp3]->value);
            auto tmp5 = tmp4->elems;
            ArrayLiteral* a = new ArrayLiteral();
            for(int i = 0; i < (int)tmp5->size(); i++){
                BasicExpr* b = new BasicExpr((*tmp5)[i]);
                a->push_back(b);
            }
            return a;
        } else {
            cerr << "Variable/parameter not in use" << endl;
            return nullptr;
        }
    } else {
        return get<ArrayLiteral*>(*tmp1);
    } 

}

// Gets an int parameter argument at index ind from constraint constr
BasicLiteralExpr* Encoder::get_const(Constraint& constr, int ind){
    auto tmp1 = (*constr.args)[ind];
    auto tmp2 = get<BasicExpr*>(*tmp1);
    auto tmp3 = get<BasicLiteralExpr*>(*tmp2);
    return tmp3;

}

// Gets an int element from an array at index ind
int Encoder::get_int_from_array(const ArrayLiteral& a, int ind){
    auto tmp1 = get<BasicLiteralExpr*>(*a[ind]);
    auto tmp2 = get<int>(*tmp1);
    return tmp2;
}

// Gets a variable element from an array at index ind
BasicVar* Encoder::get_var_from_array(const ArrayLiteral& a, int ind){
    auto tmp1 = get<string*>(*a[ind]);
    auto tmp2 = variable_map[*tmp1];
    return get<BasicVar*>(*tmp2);
}



// Checks which constraint is in question and calls the
// appropriate function to encode it
void Encoder::encode_constraint(Constraint& constr, std::vector<std::vector<Literal*>>& cnf_clauses) {
    
    
    if(*constr.name == "array_int_element"){
        auto b = get_var(constr, 0);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2);
        encode_array_int_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "array_int_maximum"){
        auto m = get_var(constr, 0);
        auto x = get_array(constr, 1);
        encode_array_int_maximum(*m, *x, cnf_clauses);
    } else if(*constr.name == "array_int_minimum"){
        auto m = get_var(constr, 0);
        auto x = get_array(constr, 1);
        encode_array_int_minimum(*m, *x, cnf_clauses);
    } else if(*constr.name == "array_var_int_element"){
        auto b = get_var(constr, 0);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2);
        encode_array_var_int_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "int_abs"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        encode_int_abs(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_div"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto c = get_var(constr, 2);
        encode_int_div(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_eq"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        encode_int_eq(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_eq_reif"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto r = get_var(constr, 2);
        encode_int_eq_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_le"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        encode_int_le(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_le_reif"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto r = get_var(constr, 2);
        encode_int_le_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_eq"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_int_lin_eq(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "int_lin_eq_reif"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3);
        encode_int_lin_eq_reif(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_le"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_int_lin_le(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "int_lin_le_reif"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3);
        encode_int_lin_le_reif(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_ne"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_int_lin_ne(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "int_lin_ne_reif"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3);
        encode_int_lin_ne_reif(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lt"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        encode_int_lt(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_lt_reif"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto r = get_var(constr, 2);
        encode_int_lt_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_max"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto c = get_var(constr, 2);
        encode_int_max(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_min"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto c = get_var(constr, 2);
        encode_int_min(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_mod"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto c = get_var(constr, 2);
        encode_int_mod(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_ne"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        encode_int_ne(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_ne_reif"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto r = get_var(constr, 2);
        encode_int_ne_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_plus"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto c = get_var(constr, 2);
        encode_int_plus(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_pow"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto c = get_var(constr, 2);
        encode_int_pow(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_times"){
        auto a = get_var(constr, 0);
        auto b = get_var(constr, 1);
        auto c = get_var(constr, 2);
        encode_int_times(*a, *b, *c, cnf_clauses);
    }

}

// ---------------------------- Encoding constraints -------------------------------------

// Primitive comparison of type: a - b <= c
bool Encoder::encode_primitive_comparison_minus(const BasicVar& a, const BasicVar& b, int c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int a_left = (*get<IntRangeVarType*>(*a.type)).left;
    int a_right = (*get<IntRangeVarType*>(*a.type)).right;
    int b_left = (*get<IntRangeVarType*>(*b.type)).left;
    int b_right = (*get<IntRangeVarType*>(*b.type)).right;

    if(c < a_left - b_right)
        return false; 

    std::vector<Literal*> curr_clause;
    for(int i = a_left - 1; i <= a_right; i++){
        for(int j = -b_right - 1; j <= -b_left; j++)
            if(i + j == c-1){
                curr_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, i));
                curr_clause.push_back(new Literal(LiteralType::ORDER, b.id, false, -j - 1));
                cnf_clauses.push_back(curr_clause);
                curr_clause.clear();
            }

    }

    return true;
}

// Primitive comparison of type: a + b <= c
bool Encoder::encode_primitive_comparison_plus(const BasicVar& a, const BasicVar& b, int c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int a_left = (*get<IntRangeVarType*>(*a.type)).left;
    int a_right = (*get<IntRangeVarType*>(*a.type)).right;
    int b_left = (*get<IntRangeVarType*>(*b.type)).left;
    int b_right = (*get<IntRangeVarType*>(*b.type)).right;

    if(c < a_left + b_left)
        return false;

    std::vector<Literal*> curr_clause;
    for(int i = a_left - 1; i <= a_right; i++){
        for(int j = b_left - 1; j <= b_right; j++){
            if(i + j == c-1){
                curr_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, i));
                curr_clause.push_back(new Literal(LiteralType::ORDER, b.id, true, j));
                cnf_clauses.push_back(curr_clause);
                curr_clause.clear();
            }
        }
    }

    return true;
}

// Reifies the temp_clauses to be equivalent to the boolean variable r
void Encoder::reify(vector<vector<Literal*>>& temp_clauses, const BasicVar& r, vector<vector<Literal*>>& cnf_clauses){
    
    vector<Literal*> helpers;
    Literal* top_helper = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
    helpers.push_back(top_helper);

    for(auto c : temp_clauses){
        Literal* helper = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
        for(auto lit : c){
            vector<Literal*> new_clause;
            new_clause.push_back(new Literal(lit->type, lit->id, lit->pol ? false : true, lit->val));
            new_clause.push_back(helper);
            cnf_clauses.push_back(new_clause);
        }
        helpers.push_back(new Literal(LiteralType::HELPER, helper->id, true, 0));
    }
    cnf_clauses.push_back(helpers);

    Literal* topmost_helper1 = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
    Literal* not_r = new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    Literal* not_top_helper = new Literal(LiteralType::HELPER, top_helper->id, true, 0);
    cnf_clauses.push_back({not_top_helper, topmost_helper1});
    cnf_clauses.push_back({not_r, topmost_helper1});

    Literal* topmost_helper2 = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
    for(auto c : temp_clauses){
        c.push_back(topmost_helper2);
        cnf_clauses.push_back(c);
    }

    Literal* yes_r = new Literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    cnf_clauses.push_back({yes_r, topmost_helper2});

    Literal* not_topmost_helper1 = new Literal(LiteralType::HELPER, topmost_helper1->id, true, 0);
    Literal* not_topmost_helper2 = new Literal(LiteralType::HELPER, topmost_helper2->id, true, 0);
    cnf_clauses.push_back({not_topmost_helper1, not_topmost_helper2});

}

// Encodes a constraint of type as[b] = c, where as is an array of int parameters
void Encoder::encode_array_int_element(const BasicVar& b, const ArrayLiteral& as, BasicVar& c, vector<vector<Literal*>>& cnf_clauses){

    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    vector<Literal*> helpers;  
    vector<Literal*> new_clause1, new_clause2;
    for(int i = b_left; i <= b_right; i++){
        if(i < 0 || i >= (int)as.size())
            continue;
        
        Literal* helper = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
        new_clause1 = { new Literal(LiteralType::ORDER, b.id, true, i), helper};
        new_clause2 = { new Literal(LiteralType::ORDER, b.id, false, i-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);

        int curr_elem = get_int_from_array(as, i);
        if(c_left > curr_elem || c_right < curr_elem){
            continue;
        }

        new_clause1 = { new Literal(LiteralType::ORDER, c.id, true, curr_elem), helper};
        new_clause2 = { new Literal(LiteralType::ORDER, c.id, false, curr_elem-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);        

        Literal* not_helper = new Literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }
    
    cnf_clauses.push_back(helpers);
}


// Encodes a constraint of type m = max(x1, x2, ... xn)
// TODO ispise UNSAT vise puta, resi
void Encoder::encode_array_int_maximum(const BasicVar& m, const ArrayLiteral& x, vector<vector<Literal*>>& cnf_clauses){

    vector<vector<Literal*>> temp_clauses;
    vector<Literal*> helpers;
    for(int i = 0; i < (int)x.size(); i++){

        auto curr_var = get_var_from_array(x, i);
        encode_int_le(m, *curr_var, temp_clauses);

        Literal* helper = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
        for(auto c : temp_clauses){
            c.push_back(helper);
            cnf_clauses.push_back(c);
        }

        Literal* not_helper = new Literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);

        encode_int_le(*curr_var, m, cnf_clauses);

        temp_clauses.clear();
    }

    cnf_clauses.push_back(helpers);
    
}

// Encodes a constraint of type m = min(x1, x2, ... xn)
void Encoder::encode_array_int_minimum(const BasicVar& m, const ArrayLiteral& x, vector<vector<Literal*>>& cnf_clauses){

    vector<vector<Literal*>> temp_clauses;
    vector<Literal*> helpers;
    for(int i = 0; i < (int)x.size(); i++){

        auto curr_var = get_var_from_array(x, i);
        encode_int_le(*curr_var, m, temp_clauses);

        Literal* helper = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
        for(auto c : temp_clauses){
            c.push_back(helper);
            cnf_clauses.push_back(c);
        }

        Literal* not_helper = new Literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);

        encode_int_le(m, *curr_var, cnf_clauses);

        temp_clauses.clear();
    }

    cnf_clauses.push_back(helpers);
    
}

// Encodes a constraint of type as[b] = c, where as is an array of int variables
void Encoder::encode_array_var_int_element(const BasicVar& b, const ArrayLiteral& as, BasicVar& c, vector<vector<Literal*>>& cnf_clauses){

    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    vector<Literal*> helpers;
    vector<vector<Literal*>> temp_clauses;   
    vector<Literal*> new_clause1, new_clause2;
    for(int i = b_left; i <= b_right; i++){
        if(i < 0 || i >= (int)as.size())
            continue;
        
        Literal* helper = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
        new_clause1 = { new Literal(LiteralType::ORDER, b.id, true, i), helper};
        new_clause2 = { new Literal(LiteralType::ORDER, b.id, false, i-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);

        auto curr_elem = get_var_from_array(as, i);

        if(c_left > get_right(curr_elem) || c_right < get_left(curr_elem)){
            continue;
        }

        encode_int_eq(c, *curr_elem, temp_clauses);
        for(auto c : temp_clauses){
            c.push_back(helper);
            cnf_clauses.push_back(c);
        }   

        Literal* not_helper = new Literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }
    
    cnf_clauses.push_back(helpers);
}



// Encodes a constraint of type |a| = b
void Encoder::encode_int_abs(const BasicVar& a, const BasicVar& b, std::vector<std::vector<Literal*>>& cnf_clauses){
    
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    if(b_left < 0){
        if(b_right < 0){
            declare_unsat();
            return;
        }
        else
            cnf_clauses.push_back({new Literal(LiteralType::ORDER, b.id, false, -1)});
    }

    int id1 = next_helper_id++;
    Literal* helper1 = new Literal(LiteralType::HELPER, id1, true, 0);

    int id2 = next_helper_id++;
    Literal* helper2 = new Literal(LiteralType::HELPER, id2, true, 0);

    std::vector<std::vector<Literal*>> new_clauses1;
    if(!encode_primitive_comparison_minus(a, b, 0, new_clauses1))
        cnf_clauses.push_back({new Literal(LiteralType::HELPER, id1, false, 0)});
    if(!encode_primitive_comparison_minus(b, a, 0, new_clauses1))
        cnf_clauses.push_back({new Literal(LiteralType::HELPER, id1, false, 0)});

    std::vector<std::vector<Literal*>> new_clauses2;    
    if(!encode_primitive_comparison_plus(b, a, 0, new_clauses2))
        cnf_clauses.push_back({new Literal(LiteralType::HELPER, id2, false, 0)});

    std::vector<std::vector<Literal*>> temp_clauses;
    if(encode_primitive_comparison_plus(a, b, -1, temp_clauses)){
        std::vector<Literal*> helpers;
        std::vector<Literal*> new_clause;
        Literal* helper;
        for(auto c : temp_clauses){
            int id = next_helper_id++;
            helper = new Literal(LiteralType::HELPER, id, true, 0);
            for(auto lit : c){
                new_clause.push_back(new Literal(LiteralType::ORDER, lit->id, lit->pol ? false : true, lit->val));
                new_clause.push_back(new Literal(LiteralType::HELPER, id, false, 0));
                new_clauses2.push_back(new_clause);
                new_clause.clear();
            }
            helpers.push_back(helper);

        }
        new_clauses2.push_back(helpers);
        temp_clauses.clear();
    }


    for(int i = 0; i < (int)new_clauses1.size(); i++){
        new_clauses1[i].push_back(new Literal(LiteralType::HELPER, id1, false, 0));
    }

    for(int i = 0; i < (int)new_clauses2.size(); i++){
        new_clauses2[i].push_back(new Literal(LiteralType::HELPER, id2, false, 0));
    }

    cnf_clauses.push_back({helper1, helper2});
    cnf_clauses.insert(cnf_clauses.end(), new_clauses1.begin(), new_clauses1.end());
    cnf_clauses.insert(cnf_clauses.end(), new_clauses2.begin(), new_clauses2.end());

}

// Encodes a constraint of type a / b = c
void Encoder::encode_int_div(const BasicVar& a, const BasicVar& b, const BasicVar& c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    int bc_left = min({b_left*c_left, b_left*c_right, b_right*c_left, b_right*c_right});
    int bc_right = max({b_left*c_left, b_left*c_right, b_right*c_left, b_right*c_right});
    BasicVar* bc = encode_int_range_helper_variable(bc_left, bc_right, cnf_clauses);
    encode_int_times(b, c, *bc, cnf_clauses);

    int r_left = 0;
    int r_right = b_right - 1;
    BasicVar* r = encode_int_range_helper_variable(r_left, r_right, cnf_clauses);
    encode_int_lt(*r, b, cnf_clauses);
    encode_int_plus(*bc, *r, a, cnf_clauses);

}

// Encodes a constraint of type a = b
void Encoder::encode_int_eq(const BasicVar& a, const BasicVar& b, std::vector<std::vector<Literal*>>& cnf_clauses){
 
    if(!encode_primitive_comparison_minus(a, b, 0, cnf_clauses)){
        declare_unsat();
        return;
    }
    if(!encode_primitive_comparison_minus(b, a, 0, cnf_clauses)){
        declare_unsat();
        return;
    }

}

// Encodes a constraint of type (a = b) <-> r
void Encoder::encode_int_eq_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, std::vector<std::vector<Literal*>>& cnf_clauses){
 
    vector<vector<Literal*>> temp_clauses;
    if(!encode_primitive_comparison_minus(a, b, 0, temp_clauses)){
        cnf_clauses.push_back({new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return;
    }
    if(!encode_primitive_comparison_minus(b, a, 0, temp_clauses)){
        cnf_clauses.push_back({new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return;
    }
    reify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type a <= b
void Encoder::encode_int_le(const BasicVar& a, const BasicVar& b, std::vector<std::vector<Literal*>>& cnf_clauses){

    if(!encode_primitive_comparison_minus(a, b, 0, cnf_clauses))
        declare_unsat();

}

//Encodes a constraint of type (a <= b) <-> r
void Encoder::encode_int_le_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, std::vector<std::vector<Literal*>>& cnf_clauses){

    vector<vector<Literal*>> temp_clauses;
    if(!encode_primitive_comparison_minus(a, b, 0, temp_clauses)){
        cnf_clauses.push_back({new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
    } else {
        reify(temp_clauses, r, cnf_clauses);
    }

}

// Encodes a substitution x = a1*x2 + a2*x2
void Encoder::encode_substitution(const BasicVar &x, const BasicVar &x1, int coef1, const BasicVar &x2, int coef2, std::vector<std::vector<Literal*>>& cnf_clauses){

    int x_left = (*get<IntRangeVarType*>(*x.type)).left;
    int x_right = (*get<IntRangeVarType*>(*x.type)).right;
    int x1_left = (*get<IntRangeVarType*>(*x1.type)).left;
    int x1_right = (*get<IntRangeVarType*>(*x1.type)).right;
    int x2_left = (*get<IntRangeVarType*>(*x2.type)).left;
    int x2_right = (*get<IntRangeVarType*>(*x2.type)).right;

    std::vector<Literal*> new_clause;

    //-x + x1 + x2 <= 0
    int lower_bound_x1 = min({coef1*x1_left, coef1*x1_right});
    int upper_bound_x1 = max({coef1*x1_left, coef1*x1_right});
    int lower_bound_x2 = min({coef2*x2_left, coef2*x2_right});
    int upper_bound_x2 = max({coef2*x2_right, coef2*x2_left});

    for(int i = -x_right - 1; i <= -x_left; i++){
        for(int j = lower_bound_x1 - 1; j <= upper_bound_x1; j++){
            for(int k = lower_bound_x2 - 1; k <= upper_bound_x2; k++){
                if(i + j + k == -2){
                    
                    new_clause.push_back(new Literal(LiteralType::ORDER, x.id, false, -i - 1));

                    if(coef1 > 0)
                        new_clause.push_back(new Literal(LiteralType::ORDER, x1.id, true, (int)floor((double)j/coef1)));
                    else 
                        new_clause.push_back(new Literal(LiteralType::ORDER, x1.id, false, (int)ceil((double)j/coef1) - 1));
                    

                    if(coef2 > 0)
                        new_clause.push_back(new Literal(LiteralType::ORDER, x2.id, true, (int)floor((double)k/coef2)));
                    else
                        new_clause.push_back(new Literal(LiteralType::ORDER, x2.id, false, (int)ceil((double)k/coef2) - 1));

                    cnf_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }    

    coef1 = -coef1;
    coef2 = -coef2;

    //x - x1 - x2 <= 0
    lower_bound_x1 = min({coef1*x1_left, coef1*x1_right});
    upper_bound_x1 = max({coef1*x1_left, coef1*x1_right});
    lower_bound_x2 = min({coef2*x2_left, coef2*x2_right});
    upper_bound_x2 = max({coef2*x2_right, coef2*x2_left});

    for(int i = x_left - 1; i <= x_right; i++){
        for(int j = lower_bound_x1 - 1; j <= upper_bound_x1; j++){
            for(int k = lower_bound_x2 - 1; k <= upper_bound_x2; k++){
                if(i + j + k == -2){

                    new_clause.push_back(new Literal(LiteralType::ORDER, x.id, true, i));

                    if(coef1 > 0)
                        new_clause.push_back(new Literal(LiteralType::ORDER, x1.id, true, (int)floor((double)j/coef1)));
                    else 
                        new_clause.push_back(new Literal(LiteralType::ORDER, x1.id, false, (int)ceil((double)j/coef1) - 1));
                    

                    if(coef2 > 0)
                        new_clause.push_back(new Literal(LiteralType::ORDER, x2.id, true, (int)floor((double)k/coef2)));
                    else
                        new_clause.push_back(new Literal(LiteralType::ORDER, x2.id, false, (int)ceil((double)k/coef2) - 1));                         
                
                    cnf_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }


}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn = c
void Encoder::encode_int_lin_eq(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }
    if(c < sum1 || c > sum2){
        declare_unsat();
        return ;
    }    

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0))});
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0) - 1)});
        return;
    }

    auto var0 = get_var_from_array(vars, 0);
    auto var1 = get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    int lower_bound1 = min({get_left(var0)*coef0, get_right(var0)*coef0});
    int upper_bound1 = max({get_left(var0)*coef0, get_right(var0)*coef0}); 
    int lower_bound2 = min({get_left(var1)*coef1, get_right(var1)*coef1});
    int upper_bound2 = max({get_left(var1)*coef1, get_right(var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_substitution(*var, *get_var_from_array(vars, 0), get_int_from_array(coefs, 0),
                        *get_var_from_array(vars, 1), get_int_from_array(coefs, 1), cnf_clauses);
    
    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(var);
        upper_bound1 = get_right(var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = get_var_from_array(vars, i);
        lower_bound2 = min({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        upper_bound2 = max({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);

        encode_substitution(*var1, *var, 1, *get_var_from_array(vars, i), get_int_from_array(coefs, i), cnf_clauses);

        var = var1;
    }

    if(vars.size() == 2){
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c)});
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, false, c - 1)});
    } else {
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var1->id, true, c)});
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var1->id, false, c - 1)});
    }
}

// Encodes a constraint of type (a1*x1 + a2*x2 + ... + an*xn = c) <-> r
void Encoder::encode_int_lin_eq_reif(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, std::vector<std::vector<Literal*>>& cnf_clauses){

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }
    if(c < sum1){
        cnf_clauses.push_back({new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return ;
    }    
    if(c > sum2){
        cnf_clauses.push_back({new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                               new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               new Literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return;
    }

    auto var0 = get_var_from_array(vars, 0);
    auto var1 = get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    int lower_bound1 = min({get_left(var0)*coef0, get_right(var0)*coef0});
    int upper_bound1 = max({get_left(var0)*coef0, get_right(var0)*coef0}); 
    int lower_bound2 = min({get_left(var1)*coef1, get_right(var1)*coef1});
    int upper_bound2 = max({get_left(var1)*coef1, get_right(var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_substitution(*var, *get_var_from_array(vars, 0), get_int_from_array(coefs, 0),
                        *get_var_from_array(vars, 1), get_int_from_array(coefs, 1), cnf_clauses);
    
    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(var);
        upper_bound1 = get_right(var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = get_var_from_array(vars, i);
        lower_bound2 = min({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        upper_bound2 = max({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);

        encode_substitution(*var1, *var, 1, *get_var_from_array(vars, i), get_int_from_array(coefs, i), cnf_clauses);

        var = var1;
    }

    vector<vector<Literal*>> temp_clauses;
    if(vars.size() == 2)
        temp_clauses.push_back({new Literal(LiteralType::ORDER, var->id, false, c - 1),
                               new Literal(LiteralType::ORDER, var->id, true, c)});
    else 
        temp_clauses.push_back({new Literal(LiteralType::ORDER, var1->id, false, c - 1),
                               new Literal(LiteralType::ORDER, var1->id, true, c)});            
    
    reify(temp_clauses, r, cnf_clauses);
}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn <= c
void Encoder::encode_int_lin_le(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int sum = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0)
            sum += coef * left;
        else
            sum += coef * right;
    }
    if(c < sum){
        declare_unsat();
        return ;
    }    

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0))});
        return;
    }

    auto var0 = get_var_from_array(vars, 0);
    auto var1 = get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    int lower_bound1 = min({get_left(var0)*coef0, get_right(var0)*coef0});
    int upper_bound1 = max({get_left(var0)*coef0, get_right(var0)*coef0}); 
    int lower_bound2 = min({get_left(var1)*coef1, get_right(var1)*coef1});
    int upper_bound2 = max({get_left(var1)*coef1, get_right(var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_substitution(*var, *get_var_from_array(vars, 0), get_int_from_array(coefs, 0),
                        *get_var_from_array(vars, 1), get_int_from_array(coefs, 1), cnf_clauses);
    
    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(var);
        upper_bound1 = get_right(var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = get_var_from_array(vars, i);
        lower_bound2 = coef_i > 0 ? get_left(var_i)*coef_i : get_right(var_i)*coef_i;
        upper_bound2 = coef_i > 0 ? get_right(var_i)*coef_i : get_left(var_i)*coef_i;
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);

        encode_substitution(*var1, *var, 1, *get_var_from_array(vars, i), get_int_from_array(coefs, i), cnf_clauses);

        var = var1;
    }

    if(vars.size() == 2)
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c)});
    else 
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var1->id, true, c)});
}

// Encodes a constraint of type (a1*x1 + a2*x2 + ... + an*xn <= c) <-> r
void Encoder::encode_int_lin_le_reif(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, std::vector<std::vector<Literal*>>& cnf_clauses){

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }
    if(c < sum1){
        cnf_clauses.push_back({new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return ;
    }    
    if(c > sum2){
        cnf_clauses.push_back({new Literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                               new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               new Literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return;
    }

    auto var0 = get_var_from_array(vars, 0);
    auto var1 = get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    int lower_bound1 = min({get_left(var0)*coef0, get_right(var0)*coef0});
    int upper_bound1 = max({get_left(var0)*coef0, get_right(var0)*coef0}); 
    int lower_bound2 = min({get_left(var1)*coef1, get_right(var1)*coef1});
    int upper_bound2 = max({get_left(var1)*coef1, get_right(var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_substitution(*var, *get_var_from_array(vars, 0), get_int_from_array(coefs, 0),
                        *get_var_from_array(vars, 1), get_int_from_array(coefs, 1), cnf_clauses);
    
    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(var);
        upper_bound1 = get_right(var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = get_var_from_array(vars, i);
        lower_bound2 = coef_i > 0 ? get_left(var_i)*coef_i : get_right(var_i)*coef_i;
        upper_bound2 = coef_i > 0 ? get_right(var_i)*coef_i : get_left(var_i)*coef_i;
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);

        encode_substitution(*var1, *var, 1, *get_var_from_array(vars, i), get_int_from_array(coefs, i), cnf_clauses);

        var = var1;
    }

    if(vars.size() == 2){
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c),
                               new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, false, c),
                               new Literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
    }
    else{
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var1->id, true, c),
                               new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var1->id, false, c),
                               new Literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
    }
}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn =/= c
void Encoder::encode_int_lin_ne(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, std::vector<std::vector<Literal*>>& cnf_clauses){   

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0) - 1),
                               new Literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0))});
        return;
    }

    auto var0 = get_var_from_array(vars, 0);
    auto var1 = get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    int lower_bound1 = min({get_left(var0)*coef0, get_right(var0)*coef0});
    int upper_bound1 = max({get_left(var0)*coef0, get_right(var0)*coef0}); 
    int lower_bound2 = min({get_left(var1)*coef1, get_right(var1)*coef1});
    int upper_bound2 = max({get_left(var1)*coef1, get_right(var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_substitution(*var, *get_var_from_array(vars, 0), get_int_from_array(coefs, 0),
                        *get_var_from_array(vars, 1), get_int_from_array(coefs, 1), cnf_clauses);
    
    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(var);
        upper_bound1 = get_right(var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = get_var_from_array(vars, i);
        lower_bound2 = min({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        upper_bound2 = max({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;

        var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);

        encode_substitution(*var1, *var, 1, *get_var_from_array(vars, i), get_int_from_array(coefs, i), cnf_clauses);

        var = var1;
    }

    if(vars.size() == 2)
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c - 1),
                               new Literal(LiteralType::ORDER, var->id, false, c)});
    else 
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var1->id, true, c - 1),
                               new Literal(LiteralType::ORDER, var1->id, false, c)});
}

// Encodes a constraint of type (a1*x1 + a2*x2 + ... + an*xn =/= c) <-> r
void Encoder::encode_int_lin_ne_reif(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, std::vector<std::vector<Literal*>>& cnf_clauses){

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }
    if(c < sum1){
        cnf_clauses.push_back({new Literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return ;
    }    
    if(c > sum2){
        cnf_clauses.push_back({new Literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                               new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               new Literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return;
    }

    auto var0 = get_var_from_array(vars, 0);
    auto var1 = get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    int lower_bound1 = min({get_left(var0)*coef0, get_right(var0)*coef0});
    int upper_bound1 = max({get_left(var0)*coef0, get_right(var0)*coef0}); 
    int lower_bound2 = min({get_left(var1)*coef1, get_right(var1)*coef1});
    int upper_bound2 = max({get_left(var1)*coef1, get_right(var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_substitution(*var, *get_var_from_array(vars, 0), get_int_from_array(coefs, 0),
                        *get_var_from_array(vars, 1), get_int_from_array(coefs, 1), cnf_clauses);
    
    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(var);
        upper_bound1 = get_right(var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = get_var_from_array(vars, i);
        lower_bound2 = min({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        upper_bound2 = max({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);

        encode_substitution(*var1, *var, 1, *get_var_from_array(vars, i), get_int_from_array(coefs, i), cnf_clauses);

        var = var1;
    }

    vector<vector<Literal*>> temp_clauses;
    if(vars.size() == 2)
        temp_clauses.push_back({new Literal(LiteralType::ORDER, var->id, true, c - 1),
                               new Literal(LiteralType::ORDER, var->id, false, c)});
    else 
        temp_clauses.push_back({new Literal(LiteralType::ORDER, var1->id, true, c - 1),
                               new Literal(LiteralType::ORDER, var1->id, false, c)});            
    
    reify(temp_clauses, r, cnf_clauses);
}

// Encode constraint of type a < b
void Encoder::encode_int_lt(const BasicVar& a, const BasicVar& b, std::vector<std::vector<Literal*>>& cnf_clauses){

    if(!encode_primitive_comparison_minus(a, b, -1, cnf_clauses))
        declare_unsat();

}

// Encode constraint of type (a < b) <-> r
void Encoder::encode_int_lt_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, std::vector<std::vector<Literal*>>& cnf_clauses){

    vector<vector<Literal*>> temp_clauses;
    if(!encode_primitive_comparison_minus(a, b, -1, temp_clauses)){
        cnf_clauses.push_back({new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
    } else {
        reify(temp_clauses, r, cnf_clauses);
    }

}

// Encode constraint of type max(a, b) = c
void Encoder::encode_int_max(const BasicVar& a, const BasicVar& b, const BasicVar& c, std::vector<std::vector<Literal*>>& cnf_clauses){

    if(!encode_primitive_comparison_minus(a, c, 0, cnf_clauses)){
        declare_unsat();
        return;
    }
    if(!encode_primitive_comparison_minus(b, c, 0, cnf_clauses)){
        declare_unsat();
        return;
    }

    int id = next_helper_id++;
    Literal* helper1 = new Literal(LiteralType::HELPER, id, true, 0);
    std::vector<std::vector<Literal*>> temp_clauses;
    int i = 0;
    if(!encode_primitive_comparison_minus(c, a, 0, temp_clauses)){
        cnf_clauses.push_back({new Literal(LiteralType::HELPER, id, false, 0)});
    } else {    
        for(i = 0; i < (int)temp_clauses.size(); i++){
            temp_clauses[i].push_back(new Literal(LiteralType::HELPER, id, false, 0));
        }
    }

    id = next_helper_id++;
    Literal* helper2 = new Literal(LiteralType::HELPER, id, true, 0);
    if(!encode_primitive_comparison_minus(c, b, 0, temp_clauses)){
        cnf_clauses.push_back({new Literal(LiteralType::HELPER, id, false, 0)});
    } else {
        for(int j = i; j < (int)temp_clauses.size(); j++){
            temp_clauses[j].push_back(new Literal(LiteralType::HELPER, id, false, 0));
        }
    }

    temp_clauses.push_back({helper1, helper2});
    cnf_clauses.insert(cnf_clauses.end(), temp_clauses.begin(), temp_clauses.end());

}

// Encode constraint of type min(a, b) = c
void Encoder::encode_int_min(const BasicVar& a, const BasicVar& b, const BasicVar& c, std::vector<std::vector<Literal*>>& cnf_clauses){
    
    if(!encode_primitive_comparison_minus(c, a, 0, cnf_clauses)){
        declare_unsat();
        return;
    }
    if(!encode_primitive_comparison_minus(c, b, 0, cnf_clauses)){
        declare_unsat();
        return;
    }

    int id = next_helper_id++;
    Literal* helper1 = new Literal(LiteralType::HELPER, id, true, 0);
    std::vector<std::vector<Literal*>> temp_clauses;
    int i = 0;
    if(!encode_primitive_comparison_minus(a, c, 0, temp_clauses)){
        cnf_clauses.push_back({new Literal(LiteralType::HELPER, id, false, 0)});
    } else {    
        for(i = 0; i < (int)temp_clauses.size(); i++){
            temp_clauses[i].push_back(new Literal(LiteralType::HELPER, id, false, 0));
        }
    }

    id = next_helper_id++;
    Literal* helper2 = new Literal(LiteralType::HELPER, id, true, 0);
    if(!encode_primitive_comparison_minus(b, c, 0, temp_clauses)){
        cnf_clauses.push_back({new Literal(LiteralType::HELPER, id, false, 0)});
    } else {
        for(int j = i; j < (int)temp_clauses.size(); j++){
            temp_clauses[j].push_back(new Literal(LiteralType::HELPER, id, false, 0));
        }
    }

    temp_clauses.push_back({helper1, helper2});
    cnf_clauses.insert(cnf_clauses.end(), temp_clauses.begin(), temp_clauses.end());

}

// Encodes a constraint of type a % b = c
void Encoder::encode_int_mod(const BasicVar& a, const BasicVar& b, const BasicVar& c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);

    int p_left = min({a_left/b_left, a_left/b_right, a_right/b_left, a_right/b_right});
    int p_right = max({a_left/b_left, a_left/b_right, a_right/b_left, a_right/b_right});
    BasicVar* p = encode_int_range_helper_variable(p_left, p_right, cnf_clauses);
    int bp_left = min({b_left*p_left, b_left*p_right, b_right*p_left, b_right*p_right});
    int bp_right = max({b_left*p_left, b_left*p_right, b_right*p_left, b_right*p_right});
    BasicVar* bp = encode_int_range_helper_variable(bp_left, bp_right, cnf_clauses);    
    encode_int_times(b, *p, *bp, cnf_clauses);

    cnf_clauses.push_back({new Literal(LiteralType::ORDER, c.id, false, -1)});
    encode_int_lt(c, b, cnf_clauses);
    encode_int_plus(*bp, c, a, cnf_clauses);

}

// Encode constraint of type a =/= b
void Encoder::encode_int_ne(const BasicVar& a, const BasicVar& b, std::vector<std::vector<Literal*>>& cnf_clauses){

    int id1 = next_helper_id++;
    int id2 = next_helper_id++;

    Literal* helper1 = new Literal(LiteralType::HELPER, id1, true, 0);
    Literal* helper2 = new Literal(LiteralType::HELPER, id2, true, 0);
    cnf_clauses.push_back({helper1, helper2});

    std::vector<std::vector<Literal*>> temp_clauses; 
    if(!encode_primitive_comparison_minus(a, b, -1, temp_clauses)){
        cnf_clauses.push_back({new Literal(LiteralType::HELPER, id1, false, 0)});
    } else {
        for(int i = 0; i < (int)temp_clauses.size(); i++)
            temp_clauses[i].push_back(new Literal(LiteralType::HELPER, id1, false, 0));

        for(auto clause : temp_clauses)
            cnf_clauses.push_back(clause);
    }

    temp_clauses.clear();
    
    if(!encode_primitive_comparison_minus(b, a, -1, temp_clauses)){
        cnf_clauses.push_back({new Literal(LiteralType::HELPER, id2, false, 0)});
    } else {
        for(int i = 0; i < (int)temp_clauses.size(); i++)
            temp_clauses[i].push_back(new Literal(LiteralType::HELPER, id2, false, 0));

        for(auto clause : temp_clauses)
            cnf_clauses.push_back(clause);
    }
}

// Encode constraint of type (a =/= b) <-> r
void Encoder::encode_int_ne_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, std::vector<std::vector<Literal*>>& cnf_clauses){

    vector<vector<Literal*>> temp_clauses1;
    encode_primitive_comparison_minus(a, b, -1, temp_clauses1);

    vector<vector<Literal*>> temp_clauses2;
    encode_primitive_comparison_minus(b, a, -1, temp_clauses2);

    Literal* helper1 = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
    Literal* helper2 = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
    Literal* yes_r = new Literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    Literal* not_r = new Literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);


    for(auto c : temp_clauses1){
        c.push_back(helper1);
        cnf_clauses.push_back(c);
    }

    for(auto c : temp_clauses2){
        c.push_back(helper2);
        cnf_clauses.push_back(c);
    }
    
    Literal* not_helper1 = new Literal(LiteralType::HELPER, helper1->id, true, 0);
    Literal* not_helper2 = new Literal(LiteralType::HELPER, helper2->id, true, 0);
   
    cnf_clauses.push_back({not_r, not_helper1, not_helper2});
    
    vector<Literal*> helpers;
    for(auto c : temp_clauses1){
        Literal* helper = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
        for(auto l : c){
            vector<Literal*> new_clause;
            new_clause.push_back(helper);
            new_clause.push_back(new Literal(LiteralType::ORDER, l->id, l->pol ? false : true, l->val));
            cnf_clauses.push_back(new_clause);
        }
        Literal* not_helper = new Literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }

    helpers.push_back(yes_r);
    cnf_clauses.push_back(helpers);

    helpers.clear();

    for(auto c : temp_clauses2){
        Literal* helper = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
        for(auto l : c){
            vector<Literal*> new_clause;
            new_clause.push_back(helper);
            new_clause.push_back(new Literal(LiteralType::ORDER, l->id, l->pol ? false : true, l->val));
            cnf_clauses.push_back(new_clause);
        }
        Literal* not_helper = new Literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }

    helpers.push_back(yes_r);
    cnf_clauses.push_back(helpers);

}

// Encode constraint of type a + b = c
void Encoder::encode_int_plus(const BasicVar& a, const BasicVar& b, const BasicVar& c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    if(a_left + b_left > c_right || a_right + b_right < c_left){
        declare_unsat();
        return;
    }

    std::vector<Literal*> new_clause;

    //-c + a + b <= 0
    for(int i = -c_right - 1; i <= -c_left; i++){
        for(int j = a_left - 1; j <= a_right; j++){
            for(int k = b_left - 1; k <= b_right; k++){
                if(i + j + k == -2){
                    
                    new_clause.push_back(new Literal(LiteralType::ORDER, c.id, false, -i - 1));
                    new_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, j));
                    new_clause.push_back(new Literal(LiteralType::ORDER, b.id, true, k));

                    cnf_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }    

    //c - a - b <= 0
    for(int i = c_left - 1; i <= c_right; i++){
        for(int j = -a_right - 1; j <= -a_left; j++){
            for(int k = -b_right - 1; k <= -b_left; k++){
                if(i + j + k == -2){

                    new_clause.push_back(new Literal(LiteralType::ORDER, c.id, true, i));
                    new_clause.push_back(new Literal(LiteralType::ORDER, a.id, false, -j - 1)); 
                    new_clause.push_back(new Literal(LiteralType::ORDER, b.id, false, -k - 1));                         
                
                    cnf_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }

}

// Encode constraint of type a^b = c, where all domains are nonnegative
// TODO specijalni slucajevi
void Encoder::encode_int_pow_nonnegative(const BasicVar& a, const BasicVar& b, const BasicVar& c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    vector<Literal*> new_clause;
    for(int i = a_left; i <= a_right; i++){
        for(int j = b_left; j <= b_right; j++){
            if(pow(i, j) >= c_right)
                continue;
            else if(pow(i, j) < c_left){
                new_clause.push_back(new Literal(LiteralType::ORDER, a.id, false, i));
                new_clause.push_back(new Literal(LiteralType::ORDER, b.id, false, j));
                cnf_clauses.push_back(new_clause);
            } else {
                new_clause.push_back(new Literal(LiteralType::ORDER, c.id, true, pow(i, j)));
                new_clause.push_back(new Literal(LiteralType::ORDER, a.id, false, i));
                new_clause.push_back(new Literal(LiteralType::ORDER, b.id, false, j));
                cnf_clauses.push_back(new_clause);                
            }
            new_clause.clear();
        }
    }

    for(int i = a_left; i <= a_right; i++){
        for(int j = b_left; j <= b_right; j++){
            if(pow(i, j) <= c_left)
                continue;
            else if(pow(i, j) > c_right){
                new_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, i - 1));
                new_clause.push_back(new Literal(LiteralType::ORDER, b.id, true, j - 1));
                cnf_clauses.push_back(new_clause);
            } else {
                new_clause.push_back(new Literal(LiteralType::ORDER, c.id, false, pow(i, j) - 1));
                new_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, i - 1));
                new_clause.push_back(new Literal(LiteralType::ORDER, b.id, true, j - 1));
                cnf_clauses.push_back(new_clause);                
            }
            new_clause.clear();
        }
    }

}

// Encode constraint of type a^b = c
// TODO napravi da bude jedna dvostruka petlja
void Encoder::encode_int_pow(const BasicVar& a, const BasicVar& b, const BasicVar& c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    if(b_right < 0){
        declare_unsat();
        return;
    } else if(b_left < 0){
        cnf_clauses.push_back({new Literal(LiteralType::ORDER, b.id, false, -1)});
    }

    if(a_left >= 0 && c_left >= 0){
        encode_int_pow_nonnegative(a, b, c, cnf_clauses);
        return;
    }

    encode_direct(a, cnf_clauses);
    encode_direct(b, cnf_clauses);
    encode_direct(c, cnf_clauses);

    vector<Literal*> helpers;
    for(int i = a_left; i <= a_right; i++)
        for(int j = b_left; j <= b_right; j++){
            if(pow(i, j) >= c_left && pow(i, j) <= c_right){
                Literal* helper = new Literal(LiteralType::HELPER, next_helper_id++, false, 0);
                helpers.push_back(new Literal(LiteralType::HELPER, helper->id, true, 0));
                vector<Literal*> new_clause1 = {helper, new Literal(LiteralType::DIRECT, a.id, true, i)};
                vector<Literal*> new_clause2 = {helper, new Literal(LiteralType::DIRECT, b.id, true, j)};
                vector<Literal*> new_clause3 = {helper, new Literal(LiteralType::DIRECT, c.id, true, pow(i, j))};
                cnf_clauses.push_back(new_clause1);
                cnf_clauses.push_back(new_clause2);
                cnf_clauses.push_back(new_clause3);
            }
        }

    cnf_clauses.push_back(helpers);
}

// Encode constraint of type a * b = c, where all domains are nonnegative
// TODO napravi da bude jedna dvostruka petlja
void Encoder::encode_int_times_nonnegative(const BasicVar& a, const BasicVar& b, const BasicVar& c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    vector<Literal*> new_clause;
    for(int i = a_left; i <= a_right; i++){
        for(int j = b_left; j <= b_right; j++){
            if(i*j >= c_right)
                continue;
            else if(i*j < c_left){
                new_clause.push_back(new Literal(LiteralType::ORDER, a.id, false, i));
                new_clause.push_back(new Literal(LiteralType::ORDER, b.id, false, j));
                cnf_clauses.push_back(new_clause);
            } else {
                new_clause.push_back(new Literal(LiteralType::ORDER, c.id, true, i*j));
                new_clause.push_back(new Literal(LiteralType::ORDER, a.id, false, i));
                new_clause.push_back(new Literal(LiteralType::ORDER, b.id, false, j));
                cnf_clauses.push_back(new_clause);                
            }
            new_clause.clear();
        }
    }

    for(int i = a_left; i <= a_right; i++){
        for(int j = b_left; j <= b_right; j++){
            if(i*j <= c_left)
                continue;
            else if(i*j > c_right){
                new_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, i - 1));
                new_clause.push_back(new Literal(LiteralType::ORDER, b.id, true, j - 1));
                cnf_clauses.push_back(new_clause);
            } else {
                new_clause.push_back(new Literal(LiteralType::ORDER, c.id, false, i*j - 1));
                new_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, i - 1));
                new_clause.push_back(new Literal(LiteralType::ORDER, b.id, true, j - 1));
                cnf_clauses.push_back(new_clause);                
            }
            new_clause.clear();
        }
    }

}

// Encode constraint of type a * b = c
// TODO napravi da bude jedna dvostruka petlja
void Encoder::encode_int_times(const BasicVar& a, const BasicVar& b, const BasicVar& c, std::vector<std::vector<Literal*>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    if(a_left >= 0 && b_left >= 0 && c_left >= 0){
        encode_int_times_nonnegative(a, b, c, cnf_clauses);
        return;
    }

    for(int ma = a_left; ma <= a_right; ma++){
        for(int Ma = ma; Ma <= a_right; Ma++){
            for(int mb = b_left; mb <= b_right; mb++){
                for(int Mb = mb; Mb <= b_right; Mb++){
                    int curr_max = max({ma*mb, ma*Mb, Ma*mb, Ma*Mb});
                    vector<Literal*> new_clause;

                    if(c_right <= curr_max)
                        continue;
                    else if(c_left > curr_max){
                        new_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(new Literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(new Literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(new Literal(LiteralType::ORDER, b.id, false, Mb));
                        cnf_clauses.push_back(new_clause);    
                    } else {
                        new_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(new Literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(new Literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(new Literal(LiteralType::ORDER, b.id, false, Mb));
                        new_clause.push_back(new Literal(LiteralType::ORDER, c.id, true, curr_max));
                        cnf_clauses.push_back(new_clause);  
                    }
                }
            }
        } 
    }

    for(int ma = a_left; ma <= a_right; ma++){
        for(int Ma = ma; Ma <= a_right; Ma++){
            for(int mb = b_left; mb <= b_right; mb++){
                for(int Mb = mb; Mb <= b_right; Mb++){
                    int curr_min = min({ma*mb, ma*Mb, Ma*mb, Ma*Mb});
                    vector<Literal*> new_clause;

                    if(c_left >= curr_min)
                        continue;
                    else if(c_right < curr_min){
                        new_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(new Literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(new Literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(new Literal(LiteralType::ORDER, b.id, false, Mb));
                        cnf_clauses.push_back(new_clause);    
                    } else {
                        new_clause.push_back(new Literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(new Literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(new Literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(new Literal(LiteralType::ORDER, b.id, false, Mb));
                        new_clause.push_back(new Literal(LiteralType::ORDER, c.id, false, curr_min - 1));                        
                        cnf_clauses.push_back(new_clause);  
                    }
                }
            }
        } 
    }

}
