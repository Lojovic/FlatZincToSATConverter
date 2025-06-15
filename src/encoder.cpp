#include "encoder.hpp"

Encoder::Encoder(const vector<Item> &items, const string& fileName) : items(items), fileName(fileName) { }

// Declares the problem to be unsat
void Encoder::declare_unsat(){
    cout << "UNSAT" << endl;
    unsat = true;
}

// Passes through the list of items which constitute the problem
// and calls the appropriate encoder function
vector<vector<shared_ptr<Literal>>> Encoder::encode_to_cnf() {

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
                cerr << "Unknown item type in encoder" << endl;
                break;
            }
    }

    return cnf_clauses;
}

// Converts the encoded problem to the DIMACS format
// and writes the output to the file specified by user
void Encoder::write_to_file(){

    ofstream file("helper1.cnf");

    if (!file.is_open()){
        cerr << "Cannot open file" << endl;
        return;
    }    

    file << "p cnf " << next_dimacs_num - 1  << " " << clause_num << endl;

    file.close();

    string command = "cat helper1.cnf helper2.cnf > " + fileName;

    system(command.c_str());

    command = "rm helper1.cnf helper2.cnf";

    system(command.c_str());

}

void Encoder::write_clauses_to_file(vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    ofstream file("helper2.cnf", ios::app);

    for(const auto& c : cnf_clauses) {
        for(const auto &l : c){

            tuple<LiteralType, int, int> type_and_id = {l->type, l->id, l->val};
            if(literal_to_num.find(type_and_id) == literal_to_num.end()){
                literal_to_num[type_and_id] = next_dimacs_num++;
                if(l->type == LiteralType::ORDER || l->type == LiteralType::BOOL_VARIABLE || l->type == LiteralType::SET_ELEM)
                    num_to_literal[next_dimacs_num-1] = l;
            } 

            file << (l->pol ? literal_to_num[type_and_id] : -literal_to_num[type_and_id]) << " ";
        }
        clause_num++;
        file << 0 << endl;
    }    

    for (auto& inner : cnf_clauses) {
        inner.clear();      
    }
    cnf_clauses.clear();              

    file.close();
}

// Runs the MiniSat solver by executing the appropriate system call.
// The input in DIMACS format should be in the inputFile, and the output is
// written to the outputFile
void Encoder::run_minisat(const string& outputFile) {

    string command = "minisat " + fileName + " " + outputFile +  "> /dev/null 2>&1";

    system(command.c_str());
}

// Reads the MiniSat solver output, converts it to a human readable format
// and writes the output to cout
void Encoder::read_minisat_output(const string& outputFile) {
    ifstream output(outputFile);
    if (!output.is_open()) {
        cerr << "Cannot open file" << endl;
        return;
    }

    string sat;
    output >> sat;
    if(sat == "UNSAT"){
        declare_unsat();
        return;
    }

    cout << "SAT" << endl;

    int curr_lit_num;
    while (output >> curr_lit_num) {

        bool sign = false;
        if(curr_lit_num < 0){
            sign = true;
            curr_lit_num = -curr_lit_num;
        }

        if(num_to_literal.find(curr_lit_num) == num_to_literal.end())
            continue;

        auto l = num_to_literal[curr_lit_num].get();

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
                curr_basic_var->value = new BasicExpr(new BasicLiteralExpr(c->left));

                id_map.erase(l->id);

                if(curr_basic_var->is_output)
                    cout << *curr_basic_var->name << " = " << c->left << endl;
            } 
        } else if(holds_alternative<IntSetVarType*>(*curr_basic_var_type)){
            IntSetVarType* c = get<IntSetVarType*>(*curr_basic_var_type);
            int* left = &(*c->elems)[0];
            int* right = &(*c->elems)[c->elems->size() - 1];

            int val = l->val;
            if(!sign){
                if(*right > val)
                    *right = val;
            } else {
                if(*left < val + 1)
                    *left = val + 1;
            }

            if(*left == *right){
                curr_basic_var->value = new BasicExpr(new BasicLiteralExpr(*left));

                id_map.erase(l->id);
                
                if(curr_basic_var->is_output)
                    cout << *curr_basic_var->name << " = " << *left << endl;
            } 
        } else if(holds_alternative<SetVarType*>(*curr_basic_var_type)){
                if(!sign)
                    set_variable_map[l->id].insert(l->val);
        } else if(holds_alternative<BasicParType>(*curr_basic_var_type)){
            if(get<BasicParType>(*curr_basic_var_type) == BasicParType::BOOL){


                if(!sign){
                    curr_basic_var->value = new BasicExpr(new BasicLiteralExpr(true));
                    if(curr_basic_var->is_output)
                        cout << *curr_basic_var->name << " = true" << endl; 
                    
                } else {
                    curr_basic_var->value = new BasicExpr(new BasicLiteralExpr(false));
                    if(curr_basic_var->is_output)                  
                        cout << *curr_basic_var->name << " = false" << endl;
                } 
                id_map.erase(l->id);                    
            }
        }

    }

    for(auto set_var : set_variable_map){

        if(!(get<BasicVar*>(*id_map[set_var.first])->is_output))
            continue;

        cout << *get<BasicVar*>(*id_map[set_var.first])->name << " = {";
        if(set_var.second.empty()){
            cout << "}" << endl;
            continue;
        }

        for(auto it = set_var.second.begin(); it != prev(set_var.second.end()); it++){
            cout << *it << ", ";
        }
        
        cout << *prev(set_var.second.end()) << "}" << endl;
    }


    for(auto array : array_set){
        auto elems = array->value;

        cout << *array->name << " = array1d(1.." << array->value->size() << ",[";

        int i = 0;
        for(auto elem : *elems){
            if(holds_alternative<string*>(*elem)){

                auto var = get<BasicVar*>(*variable_map[*get<string*>(*elem)]);
                auto val = get<BasicLiteralExpr*>(*var->value);

                if(holds_alternative<IntRangeVarType*>(*var->type) || holds_alternative<IntSetVarType*>(*var->type)){
                    cout << get<int>(*val);
                } else if(holds_alternative<BasicParType>(*var->type)){
                    auto type = get<BasicParType>(*var->type);
                    
                    if(type == BasicParType::BOOL){
                        cout << get<bool>(*val);
                    } else {
                        cout << get<int>(*val);
                    }
                }
            } else {
                auto expr = get<BasicLiteralExpr*>(*elem);
                if(holds_alternative<int>(*expr)){
                    cout << get<int>(*expr);
                } else {
                    cout << get<bool>(*expr);
                }    
            }

            if(i++ < (int)elems->size() - 1)
                cout << ", ";
            else    
                cout << "]);" << endl;
        }
    }

    output.close();
}

// Encodes a parameter of the model 
void Encoder::encode_parameter(Parameter& param, vector<vector<shared_ptr<Literal>>>& cnf_clauses) {

    parameter_map[*param.name] = &param;

}

// Encodes a variable based on it's type.
void Encoder::encode_variable(Variable& var, vector<vector<shared_ptr<Literal>>>& cnf_clauses) {
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

            vector<shared_ptr<Literal>> clause1, clause2, curr_clause;
            clause1 = {make_literal(LiteralType::ORDER, new_var_id, false, left - 1)};
            clause2 = {make_literal(LiteralType::ORDER, new_var_id, true, right)};

            cnf_clauses.push_back(clause1);
            cnf_clauses.push_back(clause2);
            for(int i = left; i <= right; i++){
                curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, false, i - 1));
                curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, true, i));
                cnf_clauses.push_back(curr_clause);
                curr_clause.clear();
            }
        } else if(holds_alternative<IntSetVarType*>(*basic_var->type)){
            IntSetVarType* t = get<IntSetVarType*>(*basic_var->type);

            vector<int> v = *t->elems;
            int n = v.size();
            int left = v[0], right = v[n-1];

            vector<shared_ptr<Literal>> clause1, clause2, curr_clause;
            clause1 = {make_literal(LiteralType::ORDER, new_var_id, false, left - 1)};
            clause2 = {make_literal(LiteralType::ORDER, new_var_id, true, right)};

            cnf_clauses.push_back(clause1);
            cnf_clauses.push_back(clause2);
            for(int i = left; i <= right; i++){
                curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, false, i - 1));
                curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, true, i));
                cnf_clauses.push_back(curr_clause);
                curr_clause.clear();
            }            

            for(int i = 0; i < n - 1; i++){
                if(v[i+1] - v[i] > 0){
                    curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, true, v[i]));
                    curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, false, v[i+1]-1));
                    cnf_clauses.push_back(curr_clause);
                    curr_clause.clear();  
                }              
            }

        } else if(holds_alternative<SetVarType*>(*basic_var->type)){
            set_variable_map[basic_var->id] = {};

            SetVarType* t = get<SetVarType*>(*basic_var->type);

            vector<int> v = *t->elems;
            for(int elem : v){
                shared_ptr<Literal> yes_l = make_literal(LiteralType::SET_ELEM, basic_var->id, true, elem);
                shared_ptr<Literal> not_l = make_literal(LiteralType::SET_ELEM, basic_var->id, false, elem);
                cnf_clauses.push_back({move(yes_l), move(not_l)});
            }

        } else if(holds_alternative<BasicParType>(*basic_var->type)){
            if(get<BasicParType>(*basic_var->type) == BasicParType::BOOL){
                vector<shared_ptr<Literal>> clause;
                clause.push_back(make_literal(LiteralType::BOOL_VARIABLE, basic_var->id, true, 0));
                clause.push_back(make_literal(LiteralType::BOOL_VARIABLE, basic_var->id, false, 0));  
                cnf_clauses.push_back(clause);
            }
        }
    } else {
        ArrayVar* array_var = get<ArrayVar*>(var);
        variable_map[*array_var->name] = &var;  
        
        if(array_var->is_output)
            array_set.insert(array_var);
    }
}

// Encodes a helper variable for substitutions
BasicVar* Encoder::encode_int_range_helper_variable(const int left, const int right, vector<vector<shared_ptr<Literal>>>& cnf_clauses) {

    int sub_id = next_var_id++;
    auto var_type = new IntRangeVarType(left, right);
    string* name = new string(format("sub_{}", sub_id));
    auto int_range_var = new BasicVar(new BasicVarType(var_type), name, true);
    int_range_var->id = sub_id;

    // variable_map[*int_range_var->name] = new Variable(int_range_var);
    // id_map[sub_id] = variable_map[*int_range_var->name];

    helper_vars.push_back(int_range_var);

    vector<shared_ptr<Literal>> clause1, clause2, curr_clause;
    clause1 = {make_literal(LiteralType::ORDER, sub_id, false, left - 1)};
    clause2 = {make_literal(LiteralType::ORDER, sub_id, true, right)};

    cnf_clauses.push_back(clause1);
    cnf_clauses.push_back(clause2);
    for(int i = left; i <= right; i++){
        curr_clause.push_back(make_literal(LiteralType::ORDER, sub_id, false, i - 1));
        curr_clause.push_back(make_literal(LiteralType::ORDER, sub_id, true, i));

        cnf_clauses.push_back(curr_clause);
        curr_clause.clear();
    }    

    return int_range_var;
}

// Encodes a bool helper variable 
BasicVar* Encoder::encode_bool_helper_variable(vector<vector<shared_ptr<Literal>>>& cnf_clauses) {

    int sub_id = next_var_id++;
    auto var_type = new BasicVarType(BasicParType::BOOL);
    string* name = new string(format("sub_{}", sub_id));

    auto bool_var = new BasicVar(var_type, name, true);
    bool_var->id = sub_id;
    cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, sub_id, true, 0),
                           make_literal(LiteralType::BOOL_VARIABLE, sub_id, false, 0)});

    helper_vars.push_back(bool_var);

    return bool_var;
}

// Gets the left border of an int variable
int get_left(const BasicVar* var){
    if(holds_alternative<IntRangeVarType*>(*var->type))
        return get<IntRangeVarType*>(*var->type)->left;
    else if(holds_alternative<IntSetVarType*>(*var->type))
        return (*get<IntSetVarType*>(*var->type)->elems)[0];
    else 
        return 0;
}

// Gets the right border of an int variable
int get_right(const BasicVar* var){
    if(holds_alternative<IntRangeVarType*>(*var->type))
        return get<IntRangeVarType*>(*var->type)->right;
    else if(holds_alternative<IntSetVarType*>(*var->type))
        return (*get<IntSetVarType*>(*var->type)->elems)[get<IntSetVarType*>(*var->type)->elems->size()-1];
    else
        return 1;
}

// Makes a connection between a direct and order encoding of a variable.
// The variable is supposed to already be encoded using the order encoding
void Encoder::encode_direct(const BasicVar& var, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    
    int left = get_left(&var);
    int right = get_right(&var);

    for(int i = left; i <= right; i++){
        shared_ptr<Literal> p = make_literal(LiteralType::DIRECT, var.id, true, i);
        shared_ptr<Literal> q = make_literal(LiteralType::ORDER, var.id, true, i);
        shared_ptr<Literal> r = make_literal(LiteralType::ORDER, var.id, true, i-1);
        shared_ptr<Literal> not_p = make_literal(LiteralType::DIRECT, var.id, false, i);
        shared_ptr<Literal> not_q = make_literal(LiteralType::ORDER, var.id, false, i);
        shared_ptr<Literal> not_r = make_literal(LiteralType::ORDER, var.id, false, i-1);

        vector<shared_ptr<Literal>> new_clause1 = {not_p, q};
        vector<shared_ptr<Literal>> new_clause2 = {not_p, not_r};
        vector<shared_ptr<Literal>> new_clause3 = {p, not_q, r};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);
        cnf_clauses.push_back(new_clause3);
    }

}

BasicVar* Encoder::encode_param_as_var(Parameter& param, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    
    auto val = param.value;
    auto type = get<BasicParType>(*param.type);
    if(type == BasicParType::INT){
        int int_val = get<int>(*get<BasicLiteralExpr*>(*val));
        return encode_int_range_helper_variable(int_val, int_val, cnf_clauses);
    } else if(type == BasicParType::BOOL){
        bool bool_val = get<bool>(*get<BasicLiteralExpr*>(*val));
        int sub_id = next_var_id++;
        auto var_type = new BasicVarType(BasicParType::BOOL);
        string* name = new string(format("sub_{}", sub_id));

        auto bool_var = new BasicVar(var_type, name, true);
        bool_var->id = sub_id;
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, sub_id, bool_val ? true : false, 0)});

        return bool_var;
    } else {
        auto set_vals = get<SetLiteral*>(*get<BasicLiteralExpr*>(*val));
        vector<int>* elems = new vector<int>;
        if(holds_alternative<SetSetLiteral*>(*set_vals))
            elems = get<SetSetLiteral*>(*set_vals)->elems;
        else {
            auto tmp =*get<SetRangeLiteral*>(*set_vals);
            int left = tmp.left;
            int right = tmp.right;
            for(int i = left; i <= right; i++){
                elems->push_back(i);
            }
        }

        int sub_id = next_var_id++;
        auto var_type = new BasicVarType(new SetVarType(elems));
        string* name = new string(format("sub_{}", sub_id));

        auto set_var = new BasicVar(var_type, name, true);
        set_var->id = sub_id;

        for(auto elem : *elems){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, sub_id, true, elem)});
        }

        return set_var;
    }
    
}

// Gets a variable argument at index ind from constraint constr
BasicVar* Encoder::get_var(Constraint& constr, int ind, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    auto tmp1 = (*constr.args)[ind];
    auto tmp2 = get<BasicExpr*>(*tmp1);
    
    if(holds_alternative<string*>(*tmp2)){
        auto tmp3 = get<string*>(*tmp2);
        
        if(variable_map.find(*tmp3) != variable_map.end())
            return get<BasicVar*>(*variable_map[*tmp3]);
        else{
            auto param = *parameter_map[*tmp3];
            return encode_param_as_var(param, cnf_clauses);
        }
    } else {
        auto type = get<BasicLiteralExpr*>(*tmp2);
        if(holds_alternative<int>(*type)){
            int int_val = get<int>(*type);
            return encode_int_range_helper_variable(int_val, int_val, cnf_clauses);
        } else if(holds_alternative<bool>(*type)){
            bool bool_val = get<bool>(*type);
            int sub_id = next_var_id++;
            auto var_type = new BasicVarType(BasicParType::BOOL);
            string* name = new string(format("sub_{}", sub_id));

            auto bool_var = new BasicVar(var_type, name, true);
            bool_var->id = sub_id;
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, sub_id, bool_val ? true : false, 0)});

            return bool_var;
        } else {
            auto set_vals = get<SetLiteral*>(*type);
            vector<int>* elems = new vector<int>;
            if(holds_alternative<SetSetLiteral*>(*set_vals))
                elems = get<SetSetLiteral*>(*set_vals)->elems;
            else {
                auto tmp =*get<SetRangeLiteral*>(*set_vals);
                int left = tmp.left;
                int right = tmp.right;
                for(int i = left; i <= right; i++){
                    elems->push_back(i);
                }
            }

            int sub_id = next_var_id++;
            auto var_type = new BasicVarType(new SetVarType(elems));
            string* name = new string(format("sub_{}", sub_id));

            auto set_var = new BasicVar(var_type, name, true);
            set_var->id = sub_id;

            for(auto elem : *elems){
                cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, sub_id, true, elem)});
            }

            return set_var;
        }
    }

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

            allocated_arrays.push_back(a);
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
    if(holds_alternative<BasicLiteralExpr*>(*tmp2)){
        auto tmp3 = get<BasicLiteralExpr*>(*tmp2);
        return tmp3;
    } else {
        string name = *get<string*>(*tmp2);
        auto param = parameter_map[name];
        auto val = param->value;
        return get<BasicLiteralExpr*>(*val);
    }

}

// Gets a set element from an array at index ind
SetLiteral* Encoder::get_set_from_array(const ArrayLiteral& a, int ind){
    auto tmp1 = *(a[ind]);
    if(holds_alternative<BasicLiteralExpr*>(tmp1)){
        auto tmp2 = get<BasicLiteralExpr*>(tmp1);
        auto tmp3 = get<SetLiteral*>(*tmp2);
        return tmp3;
    } else {
        string name = *get<string*>(tmp1);
        auto param = parameter_map[name];
        auto val = param->value;
        auto tmp2 = get<BasicLiteralExpr*>(*val);
        auto tmp3 = get<SetLiteral*>(*tmp2);
        return tmp3;
    }
}


// Gets an int element from an array at index ind
int Encoder::get_int_from_array(const ArrayLiteral& a, int ind){
    auto tmp1 = get<BasicLiteralExpr*>(*a[ind]);
    auto tmp2 = get<int>(*tmp1);
    return tmp2;
}

// Gets a bool element from an array at index ind
bool Encoder::get_bool_from_array(const ArrayLiteral& a, int ind){
    auto tmp1 = get<BasicLiteralExpr*>(*a[ind]);
    auto tmp2 = get<bool>(*tmp1);
    return tmp2;
}

// Gets a variable element from an array at index ind
BasicVar* Encoder::get_var_from_array(const ArrayLiteral& a, int ind){

    auto tmp2 = a[ind];
    
    if(holds_alternative<string*>(*tmp2)){
        auto tmp3 = get<string*>(*tmp2);
        
        if(variable_map.find(*tmp3) != variable_map.end())
            return get<BasicVar*>(*variable_map[*tmp3]);
        else{
            auto param = *parameter_map[*tmp3];
            return encode_param_as_var(param, cnf_clauses);
        }
    } else {
        auto type = get<BasicLiteralExpr*>(*tmp2);
        if(holds_alternative<int>(*type)){
            int int_val = get<int>(*type);
            return encode_int_range_helper_variable(int_val, int_val, cnf_clauses);
        } else if(holds_alternative<bool>(*type)){
            bool bool_val = get<bool>(*type);
            int sub_id = next_var_id++;
            auto var_type = new BasicVarType(BasicParType::BOOL);
            string* name = new string(format("sub_{}", sub_id));

            auto bool_var = new BasicVar(var_type, name, true);
            bool_var->id = sub_id;
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, sub_id, bool_val ? true : false, 0)});

            return bool_var;
        } else {
            auto set_vals = get<SetLiteral*>(*type);
            vector<int>* elems = new vector<int>;
            if(holds_alternative<SetSetLiteral*>(*set_vals))
                elems = get<SetSetLiteral*>(*set_vals)->elems;
            else {
                auto tmp =*get<SetRangeLiteral*>(*set_vals);
                int left = tmp.left;
                int right = tmp.right;
                for(int i = left; i <= right; i++){
                    elems->push_back(i);
                }
            }

            int sub_id = next_var_id++;
            auto var_type = new BasicVarType(new SetVarType(elems));
            string* name = new string(format("sub_{}", sub_id));

            auto set_var = new BasicVar(var_type, name, true);
            set_var->id = sub_id;

            for(auto elem : *elems){
                cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, sub_id, true, elem)});
            }

            return set_var;
        }
    }
}

// Gets the elements of a set variable
vector<int>* Encoder::get_set_elems(const BasicVar& var){
    return get<SetVarType*>(*var.type)->elems;
}


// Checks which constraint is in question and calls the
// appropriate function to encode it
void Encoder::encode_constraint(Constraint& constr, vector<vector<shared_ptr<Literal>>>& cnf_clauses) {
    
    
    if(*constr.name == "array_int_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_int_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "array_int_maximum"){
        auto m = get_var(constr, 0, cnf_clauses);
        auto x = get_array(constr, 1);
        encode_array_int_maximum(*m, *x, cnf_clauses);
    } else if(*constr.name == "array_int_minimum"){
        auto m = get_var(constr, 0, cnf_clauses);
        auto x = get_array(constr, 1);
        encode_array_int_minimum(*m, *x, cnf_clauses);
    } else if(*constr.name == "array_var_int_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_var_int_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "int_abs"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_int_abs(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_div"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_div(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_eq"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_int_eq(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_eq_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_eq_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_eq_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_eq_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_le"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_int_le(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_le_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_le_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_le_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_le_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_eq"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_int_lin_eq(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "int_lin_eq_reif"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_eq_reif(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_eq_imp"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_eq_imp(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_le"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_int_lin_le(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "int_lin_le_reif"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_le_reif(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_le_imp"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_le_imp(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_ne"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_int_lin_ne(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "int_lin_ne_reif"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_ne_reif(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_ne_imp"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_ne_imp(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lt"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_int_lt(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_lt_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_lt_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_lt_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_lt_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_max"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_max(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_min"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_min(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_mod"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_mod(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_ne"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_int_ne(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_ne_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_ne_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_ne_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_ne_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_plus"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_plus(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_pow"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_pow(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_times"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_times(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "array_bool_and"){
        auto as = get_array(constr, 0);
        auto r = get_var(constr, 1, cnf_clauses);
        encode_array_bool_and(*as, *r, cnf_clauses);
    } else if(*constr.name == "array_bool_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_bool_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "array_bool_or"){
        auto as = get_array(constr, 0);
        auto r = get_var(constr, 1, cnf_clauses);
        encode_array_bool_or(*as, *r, cnf_clauses);
    } else if(*constr.name == "array_bool_xor"){
        auto as = get_array(constr, 0);
        encode_array_bool_xor(*as, cnf_clauses);
    } else if(*constr.name == "array_var_bool_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_var_bool_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "bool2int"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_bool2int(*a, *b, cnf_clauses);
    } else if(*constr.name == "bool_and"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_and(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_clause"){
        auto as = get_array(constr, 0);
        auto bs = get_array(constr, 1);
        encode_bool_clause(*as, *bs, cnf_clauses);
    } else if(*constr.name == "bool_eq"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_bool_eq(*a, *b, cnf_clauses);
    } else if(*constr.name == "bool_eq_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_eq_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_eq_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_eq_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_le"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_bool_le(*a, *b, cnf_clauses);
    } else if(*constr.name == "bool_le_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_le_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_le_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_le_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_lin_eq"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_bool_lin_eq(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "bool_lin_le"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_bool_lin_le(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "bool_lt"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_bool_lt(*a, *b, cnf_clauses);
    } else if(*constr.name == "bool_lt_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_lt_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_lt_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_lt_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_not"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_bool_not(*a, *b, cnf_clauses);
    } else if(*constr.name == "bool_or"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_or(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_xor"){
        if(constr.args->size() == 3){
            auto a = get_var(constr, 0, cnf_clauses);
            auto b = get_var(constr, 1, cnf_clauses);
            auto r = get_var(constr, 2, cnf_clauses);
            encode_bool_xor(*a, *b, *r, cnf_clauses);
        } else {
            auto a = get_var(constr, 0, cnf_clauses);
            auto b = get_var(constr, 1, cnf_clauses);
            encode_bool_xor(*a, *b, cnf_clauses);            
        }
    } else if(*constr.name == "array_set_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_set_element(*b, *as, *c, cnf_clauses);
    }  else if(*constr.name == "array_var_set_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_var_set_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "set_card"){
        auto S = get_var(constr, 0, cnf_clauses);
        auto x = get_var(constr, 1, cnf_clauses);
        encode_set_card(*S, *x, cnf_clauses);
    } else if(*constr.name == "set_diff"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_diff(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_eq"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_eq(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_eq_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_eq_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_eq_imp"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_eq_imp(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_in"){
        auto tmp1 = (*constr.args)[1];
        auto tmp2 = get<BasicExpr*>(*tmp1);
        if(holds_alternative<string*>(*tmp2)){
            if(variable_map.find(*get<string*>(*tmp2)) != variable_map.end()){
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_var(constr, 1, cnf_clauses);
                encode_set_in(*x, *S, cnf_clauses);
            } else {
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_const(constr, 1);
                encode_set_in(*x, *S, cnf_clauses);                
            }
        } else {
            auto x = get_var(constr, 0, cnf_clauses);
            auto S = get_const(constr, 1);
            encode_set_in(*x, *S, cnf_clauses);            
        }
    } else if(*constr.name == "set_in_reif"){
        auto tmp1 = (*constr.args)[1];
        auto tmp2 = get<BasicExpr*>(*tmp1);
        if(holds_alternative<string*>(*tmp2)){
            if(variable_map.find(*get<string*>(*tmp2)) != variable_map.end()){
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_var(constr, 1, cnf_clauses);
                auto r = get_var(constr, 2, cnf_clauses);
                encode_set_in_reif(*x, *S, *r, cnf_clauses);
            } else {
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_const(constr, 1);
                auto r = get_var(constr, 2, cnf_clauses);
                encode_set_in_reif(*x, *S, *r, cnf_clauses);                
            }
        } else {
            auto x = get_var(constr, 0, cnf_clauses);
            auto S = get_const(constr, 1);
            auto r = get_var(constr, 2, cnf_clauses);
            encode_set_in_reif(*x, *S, *r, cnf_clauses);            
        }
    } else if(*constr.name == "set_in_imp"){
        auto tmp1 = (*constr.args)[1];
        auto tmp2 = get<BasicExpr*>(*tmp1);
        if(holds_alternative<string*>(*tmp2)){
            if(variable_map.find(*get<string*>(*tmp2)) != variable_map.end()){
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_var(constr, 1, cnf_clauses);
                auto r = get_var(constr, 2, cnf_clauses);
                encode_set_in_imp(*x, *S, *r, cnf_clauses);
            } else {
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_const(constr, 1);
                auto r = get_var(constr, 2, cnf_clauses);
                encode_set_in_imp(*x, *S, *r, cnf_clauses);                
            }
        } else {
            auto x = get_var(constr, 0, cnf_clauses);
            auto S = get_const(constr, 1);
            auto r = get_var(constr, 2, cnf_clauses);
            encode_set_in_imp(*x, *S, *r, cnf_clauses);            
        }
    } else if(*constr.name == "set_ne"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_ne(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_ne_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_ne_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_ne_imp"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_ne_imp(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_intersect"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_intersect(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_le"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_le(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_le_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_le_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_lt"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_lt(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_lt_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_lt_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_subset"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_subset(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_subset_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_subset_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_subset_imp"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_subset_imp(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_superset"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_superset(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_superset_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_superset_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_superset_imp"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_superset_imp(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_symdiff"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_symdiff(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_union"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_union(*x, *y, *r, cnf_clauses);
    }      

    if(!helper_vars.empty())
        cleanup_helper_variables();
    if(!allocated_arrays.empty())
        cleanup_arrays();

    write_clauses_to_file(cnf_clauses);
}

// ---------------------------- Encoding Int constraints -------------------------------------

// Primitive comparison of type: a - b <= c
bool Encoder::encode_primitive_comparison_minus(const BasicVar& a, const BasicVar& b, int c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);

    if(c < a_left - b_right)
        return false; 

    vector<shared_ptr<Literal>> curr_clause;
    for(int i = a_left - 1; i <= a_right; i++){
        for(int j = -b_right - 1; j <= -b_left; j++)
            if(i + j == c-1){
                curr_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, i));
                curr_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, -j - 1));
                cnf_clauses.push_back(curr_clause);
                curr_clause.clear();
            }

    }

    return true;
}

// Primitive comparison of type: a + b <= c
bool Encoder::encode_primitive_comparison_plus(const BasicVar& a, const BasicVar& b, int c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);

    if(c < a_left + b_left)
        return false;

    vector<shared_ptr<Literal>> curr_clause;
    for(int i = a_left - 1; i <= a_right; i++){
        for(int j = b_left - 1; j <= b_right; j++){
            if(i + j == c-1){
                curr_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, i));
                curr_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, j));
                cnf_clauses.push_back(curr_clause);
                curr_clause.clear();
            }
        }
    }

    return true;
}

// Reifies the temp_clauses to be equivalent to the boolean variable r
void Encoder::reify(vector<vector<shared_ptr<Literal>>>& temp_clauses, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    
    vector<shared_ptr<Literal>> helpers;
    shared_ptr<Literal> top_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    helpers.push_back(top_helper);

    for(auto c : temp_clauses){
        shared_ptr<Literal> helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        for(auto lit : c){
            vector<shared_ptr<Literal>> new_clause;
            new_clause.push_back(make_literal(lit->type, lit->id, lit->pol ? false : true, lit->val));
            new_clause.push_back(helper);
            cnf_clauses.push_back(new_clause);
        }
        helpers.push_back(make_literal(LiteralType::HELPER, helper->id, true, 0));
    }
    cnf_clauses.push_back(helpers);

    shared_ptr<Literal> topmost_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    shared_ptr<Literal> not_top_helper = make_literal(LiteralType::HELPER, top_helper->id, true, 0);
    cnf_clauses.push_back({not_top_helper, topmost_helper1});
    cnf_clauses.push_back({not_r, topmost_helper1});

    shared_ptr<Literal> topmost_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    for(auto c : temp_clauses){
        c.push_back(topmost_helper2);
        cnf_clauses.push_back(c);
    }

    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    cnf_clauses.push_back({yes_r, topmost_helper2});

    shared_ptr<Literal> not_topmost_helper1 = make_literal(LiteralType::HELPER, topmost_helper1->id, true, 0);
    shared_ptr<Literal> not_topmost_helper2 = make_literal(LiteralType::HELPER, topmost_helper2->id, true, 0);
    cnf_clauses.push_back({not_topmost_helper1, not_topmost_helper2});

}

// Impifies the temp_clauses to be implied by the boolean variable r
void Encoder::impify(vector<vector<shared_ptr<Literal>>>& temp_clauses, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    for(auto clause : temp_clauses){
        clause.push_back(not_r);
        cnf_clauses.push_back(clause);
    }
}

// Encodes a constraint of type as[b] = c, where as is an array of int parameters
void Encoder::encode_array_int_element(const BasicVar& b, const ArrayLiteral& as, BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    vector<shared_ptr<Literal>> helpers;  
    vector<shared_ptr<Literal>> new_clause1, new_clause2;
    for(int i = b_left; i <= b_right; i++){
        if(i < 0 || i >= (int)as.size())
            continue;
        
        shared_ptr<Literal> helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        new_clause1 = { make_literal(LiteralType::ORDER, b.id, true, i), helper};
        new_clause2 = { make_literal(LiteralType::ORDER, b.id, false, i-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);

        int curr_elem = get_int_from_array(as, i);
        if(c_left > curr_elem || c_right < curr_elem){
            continue;
        }

        new_clause1 = { make_literal(LiteralType::ORDER, c.id, true, curr_elem), helper};
        new_clause2 = { make_literal(LiteralType::ORDER, c.id, false, curr_elem-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);        

        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }
    
    cnf_clauses.push_back(helpers);
}


// Encodes a constraint of type m = max(x1, x2, ... xn)
void Encoder::encode_array_int_maximum(const BasicVar& m, const ArrayLiteral& x, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    vector<shared_ptr<Literal>> helpers;
    bool found = false;
    for(int i = 0; i < (int)x.size(); i++){

        auto curr_var = get_var_from_array(x, i);
        if(encode_primitive_comparison_minus(m, *curr_var, 0, temp_clauses))
            found = true;

        shared_ptr<Literal> helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        for(auto c : temp_clauses){
            c.push_back(helper);
            cnf_clauses.push_back(c);
        }

        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);

        if(!encode_primitive_comparison_minus(*curr_var, m, 0, cnf_clauses)){
            declare_unsat();
            return;
        }

        temp_clauses.clear();
    }

    cnf_clauses.push_back(helpers);
    
    if(!found)
        declare_unsat();
}

// Encodes a constraint of type m = min(x1, x2, ... xn)
void Encoder::encode_array_int_minimum(const BasicVar& m, const ArrayLiteral& x, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    vector<shared_ptr<Literal>> helpers;
    for(int i = 0; i < (int)x.size(); i++){

        auto curr_var = get_var_from_array(x, i);
        encode_int_le(*curr_var, m, temp_clauses);

        shared_ptr<Literal> helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        for(auto c : temp_clauses){
            c.push_back(helper);
            cnf_clauses.push_back(c);
        }

        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);

        encode_int_le(m, *curr_var, cnf_clauses);

        temp_clauses.clear();
    }

    cnf_clauses.push_back(helpers);
    
}

// Encodes a constraint of type as[b] = c, where as is an array of int variables
void Encoder::encode_array_var_int_element(const BasicVar& b, const ArrayLiteral& as, BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    vector<shared_ptr<Literal>> helpers;
    vector<vector<shared_ptr<Literal>>> temp_clauses;   
    vector<shared_ptr<Literal>> new_clause1, new_clause2;
    for(int i = b_left; i <= b_right; i++){
        if(i < 0 || i >= (int)as.size())
            continue;
        
        shared_ptr<Literal> helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        new_clause1 = { make_literal(LiteralType::ORDER, b.id, true, i), helper};
        new_clause2 = { make_literal(LiteralType::ORDER, b.id, false, i-1), helper};
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

        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }
    
    cnf_clauses.push_back(helpers);
}



// Encodes a constraint of type |a| = b
void Encoder::encode_int_abs(const BasicVar& a, const BasicVar& b, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    if(b_left < 0){
        if(b_right < 0){
            declare_unsat();
            return;
        }
        else
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1)});
    }

    int id1 = next_helper_id++;
    shared_ptr<Literal> helper1 = make_literal(LiteralType::HELPER, id1, true, 0);

    int id2 = next_helper_id++;
    shared_ptr<Literal> helper2 = make_literal(LiteralType::HELPER, id2, true, 0);

    vector<vector<shared_ptr<Literal>>> new_clauses1;
    if(!encode_primitive_comparison_minus(a, b, 0, new_clauses1))
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, id1, false, 0)});
    if(!encode_primitive_comparison_minus(b, a, 0, new_clauses1))
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, id1, false, 0)});

    vector<vector<shared_ptr<Literal>>> new_clauses2;    
    if(!encode_primitive_comparison_plus(b, a, 0, new_clauses2))
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, id2, false, 0)});

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(encode_primitive_comparison_plus(a, b, -1, temp_clauses)){
        vector<shared_ptr<Literal>> helpers;
        vector<shared_ptr<Literal>> new_clause;
        shared_ptr<Literal> helper;
        for(auto c : temp_clauses){
            int id = next_helper_id++;
            helper = make_literal(LiteralType::HELPER, id, true, 0);
            for(auto lit : c){
                new_clause.push_back(make_literal(LiteralType::ORDER, lit->id, lit->pol ? false : true, lit->val));
                new_clause.push_back(make_literal(LiteralType::HELPER, id, false, 0));
                new_clauses2.push_back(new_clause);
                new_clause.clear();
            }
            helpers.push_back(helper);

        }
        new_clauses2.push_back(helpers);
        temp_clauses.clear();
    }


    for(int i = 0; i < (int)new_clauses1.size(); i++){
        new_clauses1[i].push_back(make_literal(LiteralType::HELPER, id1, false, 0));
    }

    for(int i = 0; i < (int)new_clauses2.size(); i++){
        new_clauses2[i].push_back(make_literal(LiteralType::HELPER, id2, false, 0));
    }

    cnf_clauses.push_back({helper1, helper2});
    cnf_clauses.insert(cnf_clauses.end(), new_clauses1.begin(), new_clauses1.end());
    cnf_clauses.insert(cnf_clauses.end(), new_clauses2.begin(), new_clauses2.end());

}

// Encodes a constraint of type a / b = c
void Encoder::encode_int_div(const BasicVar& a, const BasicVar& b, const BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, -1),
                           make_literal(LiteralType::ORDER, b.id, false, 0)});

    int bc_left = min({b_left*c_left, b_left*c_right, b_right*c_left, b_right*c_right});
    int bc_right = max({b_left*c_left, b_left*c_right, b_right*c_left, b_right*c_right});
    BasicVar* bc = encode_int_range_helper_variable(bc_left, bc_right, cnf_clauses);
    encode_int_times(b, c, *bc, cnf_clauses);

    if(unsat) return;

    int r_left = -(max(abs(b_left), abs(b_right))) + 1;
    int r_right = (max(abs(b_left), abs(b_right))) - 1;
    BasicVar* r = encode_int_range_helper_variable(r_left, r_right, cnf_clauses);

    if(unsat) return;

    int r_abs_left = r_left*r_right < 0 ? 0 : min(abs(r_left), abs(r_right));
    int r_abs_right = max(abs(r_left), abs(r_right));
    BasicVar* r_abs = encode_int_range_helper_variable(r_abs_left, r_abs_right, cnf_clauses);

    int b_abs_left = b_left*b_right < 0 ? 0 : min(abs(b_left), abs(b_right));
    int b_abs_right = max(abs(b_left), abs(b_right));
    BasicVar* b_abs = encode_int_range_helper_variable(b_abs_left, b_abs_right, cnf_clauses);

    encode_int_abs(*r, *r_abs, cnf_clauses);
    if(unsat) return;
    encode_int_abs(b, *b_abs, cnf_clauses);
    if(unsat) return;
    encode_int_lt(*r_abs, *b_abs, cnf_clauses);
    if(unsat) return;
    encode_int_plus(*bc, *r, a, cnf_clauses);

    shared_ptr<Literal> pos_r = make_literal(LiteralType::ORDER, r->id, false, -1);
    shared_ptr<Literal> neg_r = make_literal(LiteralType::ORDER, r->id, true, 0);

    if(a_right < 0){
        if(r_left > 0){
            declare_unsat();
            return;
        } else {
            cnf_clauses.push_back({neg_r});
        }
    } else if(a_left > 0){
        if(r_right < 0){
            declare_unsat();
            return;
        } else {
            cnf_clauses.push_back({pos_r});
        }
    } else {

        cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, true, -1),
                               pos_r});


        cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, false, 0),
                               neg_r}); 
    }                          
}

// Encodes a constraint of type a = b
void Encoder::encode_int_eq(const BasicVar& a, const BasicVar& b, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
 
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
void Encoder::encode_int_eq_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
 
    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(!encode_primitive_comparison_minus(a, b, 0, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return;
    }
    if(!encode_primitive_comparison_minus(b, a, 0, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return;
    }
    reify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type r -> (a = b)
void Encoder::encode_int_eq_imp(const BasicVar& a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
 
    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(!encode_primitive_comparison_minus(a, b, 0, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return;
    }
    if(!encode_primitive_comparison_minus(b, a, 0, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return;
    }
    impify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type a <= b
void Encoder::encode_int_le(const BasicVar& a, const BasicVar& b, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    if(!encode_primitive_comparison_minus(a, b, 0, cnf_clauses))
        declare_unsat();

}

//Encodes a constraint of type (a <= b) <-> r
void Encoder::encode_int_le_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(!encode_primitive_comparison_minus(a, b, 0, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
    } else {
        reify(temp_clauses, r, cnf_clauses);
    }

}

//Encodes a constraint of type r -> (a <= b)
void Encoder::encode_int_le_imp(const BasicVar& a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(!encode_primitive_comparison_minus(a, b, 0, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
    } else {
        impify(temp_clauses, r, cnf_clauses);
    }

}

// Encodes a substitution x = a1*x2 + a2*x2
void Encoder::encode_substitution(const BasicVar &x, const BasicVar &x1, int coef1, const BasicVar &x2, int coef2, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int x_left = get_left(&x);
    int x_right = get_right(&x);
    int x1_left = get_left(&x1);
    int x1_right = get_right(&x1);
    int x2_left = get_left(&x2);
    int x2_right = get_right(&x2);

    vector<shared_ptr<Literal>> new_clause;

    //-x + x1 + x2 <= 0
    int lower_bound_x1 = min({coef1*x1_left, coef1*x1_right});
    int upper_bound_x1 = max({coef1*x1_left, coef1*x1_right});
    int lower_bound_x2 = min({coef2*x2_left, coef2*x2_right});
    int upper_bound_x2 = max({coef2*x2_right, coef2*x2_left});

    for(int i = -x_right - 1; i <= -x_left; i++){
        for(int j = lower_bound_x1 - 1; j <= upper_bound_x1; j++){
            for(int k = lower_bound_x2 - 1; k <= upper_bound_x2; k++){
                if(i + j + k == -2){
                    
                    new_clause.push_back(make_literal(LiteralType::ORDER, x.id, false, -i - 1));

                    if(coef1 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, true, (int)floor((double)j/coef1)));
                    else 
                        new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, false, (int)ceil((double)j/coef1) - 1));
                    

                    if(coef2 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, true, (int)floor((double)k/coef2)));
                    else
                        new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, false, (int)ceil((double)k/coef2) - 1));

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

                    new_clause.push_back(make_literal(LiteralType::ORDER, x.id, true, i));

                    if(coef1 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, true, (int)floor((double)j/coef1)));
                    else 
                        new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, false, (int)ceil((double)j/coef1) - 1));
                    

                    if(coef2 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, true, (int)floor((double)k/coef2)));
                    else
                        new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, false, (int)ceil((double)k/coef2) - 1));                         
                
                    cnf_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }


}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn = c
void Encoder::encode_int_lin_eq(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0))});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0) - 1)});
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
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c - 1)});
    } else {
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, false, c - 1)});
    }
}

// Encodes a constraint of type (a1*x1 + a2*x2 + ... + an*xn = c) <-> r
void Encoder::encode_int_lin_eq_reif(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return ;
    }    
    if(c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
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

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(vars.size() == 2)
        temp_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c - 1),
                               make_literal(LiteralType::ORDER, var->id, true, c)});
    else 
        temp_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, false, c - 1),
                               make_literal(LiteralType::ORDER, var1->id, true, c)});            
    
    reify(temp_clauses, r, cnf_clauses);
}

// Encodes a constraint of type r -> (a1*x1 + a2*x2 + ... + an*xn = c)
void Encoder::encode_int_lin_eq_imp(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return ;
    }    
    if(c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
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

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(vars.size() == 2)
        temp_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c - 1),
                               make_literal(LiteralType::ORDER, var->id, true, c)});
    else 
        temp_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, false, c - 1),
                               make_literal(LiteralType::ORDER, var1->id, true, c)});            
    
    impify(temp_clauses, r, cnf_clauses);
}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn <= c
void Encoder::encode_int_lin_le(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0))});
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
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c)});
    else 
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c)});
}

// Encodes a constraint of type (a1*x1 + a2*x2 + ... + an*xn <= c) <-> r
void Encoder::encode_int_lin_le_reif(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return ;
    }    
    if(c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
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
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
    }
    else{
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, false, c),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
    }
}

// Encodes a constraint of type r -> (a1*x1 + a2*x2 + ... + an*xn <= c)
void Encoder::encode_int_lin_le_imp(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return ;
    }    
    if(c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
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
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
    }
    else{
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
    }
}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn =/= c
void Encoder::encode_int_lin_ne(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){   

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0) - 1),
                               make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0))});
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
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c - 1),
                               make_literal(LiteralType::ORDER, var->id, false, c)});
    else 
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c - 1),
                               make_literal(LiteralType::ORDER, var1->id, false, c)});
}

// Encodes a constraint of type (a1*x1 + a2*x2 + ... + an*xn =/= c) <-> r
void Encoder::encode_int_lin_ne_reif(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return ;
    }    
    if(c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
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

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(vars.size() == 2)
        temp_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c - 1),
                               make_literal(LiteralType::ORDER, var->id, false, c)});
    else 
        temp_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c - 1),
                               make_literal(LiteralType::ORDER, var1->id, false, c)});            
    
    reify(temp_clauses, r, cnf_clauses);
}

// Encodes a constraint of type r -> (a1*x1 + a2*x2 + ... + an*xn =/= c)
void Encoder::encode_int_lin_ne_imp(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return ;
    }    
    if(c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
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

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(vars.size() == 2)
        temp_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c - 1),
                               make_literal(LiteralType::ORDER, var->id, false, c)});
    else 
        temp_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c - 1),
                               make_literal(LiteralType::ORDER, var1->id, false, c)});            
    
    impify(temp_clauses, r, cnf_clauses);
}

// Encodes a constraint of type a < b
void Encoder::encode_int_lt(const BasicVar& a, const BasicVar& b, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    if(!encode_primitive_comparison_minus(a, b, -1, cnf_clauses))
        declare_unsat();

}

// Encodes a constraint of type (a < b) <-> r
void Encoder::encode_int_lt_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(!encode_primitive_comparison_minus(a, b, -1, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
    } else {
        reify(temp_clauses, r, cnf_clauses);
    }

}

// Encodes a constraint of type r -> (a < b)
void Encoder::encode_int_lt_imp(const BasicVar& a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    if(!encode_primitive_comparison_minus(a, b, -1, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
    } else {
        impify(temp_clauses, r, cnf_clauses);
    }

}

// Encodes a constraint of type max(a, b) = c
void Encoder::encode_int_max(const BasicVar& a, const BasicVar& b, const BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    if(!encode_primitive_comparison_minus(a, c, 0, cnf_clauses)){
        declare_unsat();
        return;
    }
    if(!encode_primitive_comparison_minus(b, c, 0, cnf_clauses)){
        declare_unsat();
        return;
    }

    int id = next_helper_id++;
    shared_ptr<Literal> helper1 = make_literal(LiteralType::HELPER, id, true, 0);
    vector<vector<shared_ptr<Literal>>> temp_clauses;
    int i = 0;
    if(!encode_primitive_comparison_minus(c, a, 0, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, id, false, 0)});
    } else {    
        for(i = 0; i < (int)temp_clauses.size(); i++){
            temp_clauses[i].push_back(make_literal(LiteralType::HELPER, id, false, 0));
        }
    }

    id = next_helper_id++;
    shared_ptr<Literal> helper2 = make_literal(LiteralType::HELPER, id, true, 0);
    if(!encode_primitive_comparison_minus(c, b, 0, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, id, false, 0)});
    } else {
        for(int j = i; j < (int)temp_clauses.size(); j++){
            temp_clauses[j].push_back(make_literal(LiteralType::HELPER, id, false, 0));
        }
    }

    temp_clauses.push_back({helper1, helper2});
    cnf_clauses.insert(cnf_clauses.end(), temp_clauses.begin(), temp_clauses.end());

}

// Encodes a constraint of type min(a, b) = c
void Encoder::encode_int_min(const BasicVar& a, const BasicVar& b, const BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    
    if(!encode_primitive_comparison_minus(c, a, 0, cnf_clauses)){
        declare_unsat();
        return;
    }
    if(!encode_primitive_comparison_minus(c, b, 0, cnf_clauses)){
        declare_unsat();
        return;
    }

    int id = next_helper_id++;
    shared_ptr<Literal> helper1 = make_literal(LiteralType::HELPER, id, true, 0);
    vector<vector<shared_ptr<Literal>>> temp_clauses;
    int i = 0;
    if(!encode_primitive_comparison_minus(a, c, 0, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, id, false, 0)});
    } else {    
        for(i = 0; i < (int)temp_clauses.size(); i++){
            temp_clauses[i].push_back(make_literal(LiteralType::HELPER, id, false, 0));
        }
    }

    id = next_helper_id++;
    shared_ptr<Literal> helper2 = make_literal(LiteralType::HELPER, id, true, 0);
    if(!encode_primitive_comparison_minus(b, c, 0, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, id, false, 0)});
    } else {
        for(int j = i; j < (int)temp_clauses.size(); j++){
            temp_clauses[j].push_back(make_literal(LiteralType::HELPER, id, false, 0));
        }
    }

    temp_clauses.push_back({helper1, helper2});
    cnf_clauses.insert(cnf_clauses.end(), temp_clauses.begin(), temp_clauses.end());

}

// Encodes a constraint of type a % b = c
void Encoder::encode_int_mod(const BasicVar& a, const BasicVar& b, const BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    if(b_left == 0 && b_right == 0){
        declare_unsat();
        return;
    }

    if(b_left == 0)
        b_left = 1;
    else if(b_right == 0)
        b_right = -1;

    cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, -1),
                           make_literal(LiteralType::ORDER, b.id, false, 0)});

    int p_left = min({a_left/b_left, a_left/b_right, a_right/b_left, a_right/b_right});
    int p_right = max({a_left/b_left, a_left/b_right, a_right/b_left, a_right/b_right});
    BasicVar* p = encode_int_range_helper_variable(p_left, p_right, cnf_clauses);
    int bp_left = min({b_left*p_left, b_left*p_right, b_right*p_left, b_right*p_right});
    int bp_right = max({b_left*p_left, b_left*p_right, b_right*p_left, b_right*p_right});
    BasicVar* bp = encode_int_range_helper_variable(bp_left, bp_right, cnf_clauses);    
    encode_int_times(b, *p, *bp, cnf_clauses);


    int c_abs_left = c_left*c_right < 0 ? 0 : min(abs(c_left), abs(c_right));
    int c_abs_right = max(abs(c_left), abs(c_right));
    BasicVar* c_abs = encode_int_range_helper_variable(c_abs_left, c_abs_right, cnf_clauses);

    int b_abs_left = b_left*b_right < 0 ? 0 : min(abs(b_left), abs(b_right));
    int b_abs_right = max(abs(b_left), abs(b_right));
    BasicVar* b_abs = encode_int_range_helper_variable(b_abs_left, b_abs_right, cnf_clauses);

    encode_int_abs(c, *c_abs, cnf_clauses);
    encode_int_abs(b, *b_abs, cnf_clauses);
    encode_int_lt(*c_abs, *b_abs, cnf_clauses);
    encode_int_plus(*bp, c, a, cnf_clauses);

    shared_ptr<Literal> pos_c = make_literal(LiteralType::ORDER, c.id, false, -1);
    shared_ptr<Literal> neg_c = make_literal(LiteralType::ORDER, c.id, true, 0);

    if(a_right < 0){
        if(c_left > 0){
            declare_unsat();
            return;
        } else {
            cnf_clauses.push_back({neg_c});
        }
    } else if(a_left > 0){
        if(c_right < 0){
            declare_unsat();
            return;
        } else {
            cnf_clauses.push_back({pos_c});
        }
    } else {

        cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, true, -1),
                               pos_c});


        cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, false, 0),
                               neg_c}); 
    }
}

// Encodes a constraint of type a =/= b
void Encoder::encode_int_ne(const BasicVar& a, const BasicVar& b, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int id1 = next_helper_id++;
    int id2 = next_helper_id++;

    shared_ptr<Literal> helper1 = make_literal(LiteralType::HELPER, id1, true, 0);
    shared_ptr<Literal> helper2 = make_literal(LiteralType::HELPER, id2, true, 0);
    cnf_clauses.push_back({helper1, helper2});

    vector<vector<shared_ptr<Literal>>> temp_clauses; 
    if(!encode_primitive_comparison_minus(a, b, -1, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, id1, false, 0)});
    } else {
        for(int i = 0; i < (int)temp_clauses.size(); i++)
            temp_clauses[i].push_back(make_literal(LiteralType::HELPER, id1, false, 0));

        for(auto clause : temp_clauses)
            cnf_clauses.push_back(clause);
    }

    temp_clauses.clear();
    
    if(!encode_primitive_comparison_minus(b, a, -1, temp_clauses)){
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, id2, false, 0)});
    } else {
        for(int i = 0; i < (int)temp_clauses.size(); i++)
            temp_clauses[i].push_back(make_literal(LiteralType::HELPER, id2, false, 0));

        for(auto clause : temp_clauses)
            cnf_clauses.push_back(clause);
    }
}

// Encodes a constraint of type (a =/= b) <-> r
void Encoder::encode_int_ne_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    BasicVar* r1 = encode_bool_helper_variable(cnf_clauses);
    BasicVar* r2 = encode_bool_helper_variable(cnf_clauses);

    encode_int_lt_reif(a, b, *r1, cnf_clauses);
    encode_int_lt_reif(b, a, *r2, cnf_clauses);

    shared_ptr<Literal> yes_r1 = make_literal(LiteralType::BOOL_VARIABLE, r1->id, true, 0);
    shared_ptr<Literal> not_r1 = make_literal(LiteralType::BOOL_VARIABLE, r1->id, false, 0);
    shared_ptr<Literal> yes_r2 = make_literal(LiteralType::BOOL_VARIABLE, r2->id, true, 0);
    shared_ptr<Literal> not_r2 = make_literal(LiteralType::BOOL_VARIABLE, r2->id, false, 0);

    cnf_clauses.push_back({yes_r, not_r1});
    cnf_clauses.push_back({yes_r, not_r2});
    cnf_clauses.push_back({not_r, yes_r1, yes_r2});


}

// Encodes a constraint of type r -> (a =/= b)
void Encoder::encode_int_ne_imp(const BasicVar& a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    BasicVar* r1 = encode_bool_helper_variable(cnf_clauses);
    BasicVar* r2 = encode_bool_helper_variable(cnf_clauses);

    encode_int_lt_reif(a, b, *r1, cnf_clauses);
    encode_int_lt_reif(b, a, *r2, cnf_clauses);

    cnf_clauses.push_back({not_r, make_literal(LiteralType::BOOL_VARIABLE, r1->id, true, 0),
        make_literal(LiteralType::BOOL_VARIABLE, r2->id, true, 0)});

}

// Encodes a constraint of type a + b = c
void Encoder::encode_int_plus(const BasicVar& a, const BasicVar& b, const BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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

    vector<shared_ptr<Literal>> new_clause;

    //-c + a + b <= 0
    for(int i = -c_right - 1; i <= -c_left; i++){
        for(int j = a_left - 1; j <= a_right; j++){
            for(int k = b_left - 1; k <= b_right; k++){
                if(i + j + k == -2){
                    
                    new_clause.push_back(make_literal(LiteralType::ORDER, c.id, false, -i - 1));
                    new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, j));
                    new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, k));

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

                    new_clause.push_back(make_literal(LiteralType::ORDER, c.id, true, i));
                    new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, -j - 1)); 
                    new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, -k - 1));                         
                
                    cnf_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }

}

// Encodes a constraint of type a^b = c
void Encoder::encode_int_pow(const BasicVar& a, const BasicVar& b, const BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1)});
    }

    encode_direct(a, cnf_clauses);
    encode_direct(b, cnf_clauses);
    encode_direct(c, cnf_clauses);

    vector<shared_ptr<Literal>> helpers;
    for(int i = a_left; i <= a_right; i++)
        for(int j = b_left; j <= b_right; j++){
            if(pow(i, j) >= c_left && pow(i, j) <= c_right){
                shared_ptr<Literal> helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
                helpers.push_back(make_literal(LiteralType::HELPER, helper->id, true, 0));
                vector<shared_ptr<Literal>> new_clause1 = {helper, make_literal(LiteralType::DIRECT, a.id, true, i)};
                vector<shared_ptr<Literal>> new_clause2 = {helper, make_literal(LiteralType::DIRECT, b.id, true, j)};
                vector<shared_ptr<Literal>> new_clause3 = {helper, make_literal(LiteralType::DIRECT, c.id, true, pow(i, j))};
                cnf_clauses.push_back(new_clause1);
                cnf_clauses.push_back(new_clause2);
                cnf_clauses.push_back(new_clause3);
            }
        }

    cnf_clauses.push_back(helpers);
}

// Encodes a constraint of type a * b = c, where all domains are nonnegative
void Encoder::encode_int_times_nonnegative(const BasicVar& a, const BasicVar& b, const BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    vector<shared_ptr<Literal>> new_clause;
    for(int i = a_left; i <= a_right; i++){
        for(int j = b_left; j <= b_right; j++){
            if(i*j >= c_right)
                continue;
            else if(i*j < c_left){
                new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, i));
                new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, j));
                cnf_clauses.push_back(new_clause);
            } else {
                new_clause.push_back(make_literal(LiteralType::ORDER, c.id, true, i*j));
                new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, i));
                new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, j));
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
                new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, i - 1));
                new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, j - 1));
                cnf_clauses.push_back(new_clause);
            } else {
                new_clause.push_back(make_literal(LiteralType::ORDER, c.id, false, i*j - 1));
                new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, i - 1));
                new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, j - 1));
                cnf_clauses.push_back(new_clause);                
            }
            new_clause.clear();
        }
    }

}

// Encodes a constraint of type a * b = c
void Encoder::encode_int_times(const BasicVar& a, const BasicVar& b, const BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

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
                    vector<shared_ptr<Literal>> new_clause;

                    if(c_right <= curr_max)
                        continue;
                    else if(c_left > curr_max){
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, Mb));
                        cnf_clauses.push_back(new_clause);    
                    } else {
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, Mb));
                        new_clause.push_back(make_literal(LiteralType::ORDER, c.id, true, curr_max));
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
                    vector<shared_ptr<Literal>> new_clause;

                    if(c_left >= curr_min)
                        continue;
                    else if(c_right < curr_min){
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, Mb));
                        cnf_clauses.push_back(new_clause);    
                    } else {
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, Mb));
                        new_clause.push_back(make_literal(LiteralType::ORDER, c.id, false, curr_min - 1));                        
                        cnf_clauses.push_back(new_clause);  
                    }
                }
            }
        } 
    }

}

// Encodes a constraint of type x ∈ S1
void Encoder::encode_set_in(const BasicVar& x, const BasicLiteralExpr& S1, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    
    auto S = get<SetLiteral*>(S1);
    auto left = get_left(&x);
    auto right = get_right(&x);

    vector<int> elems;
    if(holds_alternative<SetSetLiteral*>(*S)){
        elems = *get<SetSetLiteral*>(*S)->elems;
    } else {
        int left = get<SetRangeLiteral*>(*S)->left;
        int right = get<SetRangeLiteral*>(*S)->right;
        for(int i = left; i <= right; i++)
            elems.push_back(i);
    }

    if(left > elems[elems.size() - 1] || right < elems[0]){
        declare_unsat();
        return ;
    }

    vector<shared_ptr<Literal>> helpers;
    for(auto elem : elems){
        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        if(elem >= left && elem <= right){
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, elem),
                                    not_helper});
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, elem-1),
                                    not_helper});
        helpers.push_back(yes_helper);
        }
    }

    cnf_clauses.push_back(helpers);
}

// ---------------------------- Encoding Bool constraints -------------------------------------

// Encodes a constraint of type r ↔ ⋀i as[i]
void Encoder::encode_array_bool_and(const ArrayLiteral& as, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    vector<shared_ptr<Literal>> new_clause1;
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    for(int i = 0; i < (int)as.size(); i++){
        auto p = get_var_from_array(as, i);
        shared_ptr<Literal> not_p = make_literal(LiteralType::BOOL_VARIABLE, p->id, false, 0);
        shared_ptr<Literal> yes_p = make_literal(LiteralType::BOOL_VARIABLE, p->id, true, 0); 

        new_clause1.push_back(not_p);

        vector<shared_ptr<Literal>> new_clause2 = {yes_p, not_r};
        cnf_clauses.push_back(new_clause2);

    }

    new_clause1.push_back(yes_r);
    cnf_clauses.push_back(new_clause1);
}

// Encodes a constraint of type as[b] = c, where as is an array of bool parameters
void Encoder::encode_array_bool_element(const BasicVar& b, const ArrayLiteral& as, BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int b_left = get_left(&b);
    int b_right = get_right(&b);

    vector<shared_ptr<Literal>> helpers;  
    vector<shared_ptr<Literal>> new_clause1, new_clause2;
    for(int i = b_left; i <= b_right; i++){
        if(i < 0 || i >= (int)as.size())
            continue;
        
        shared_ptr<Literal> helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        new_clause1 = { make_literal(LiteralType::ORDER, b.id, true, i), helper};
        new_clause2 = { make_literal(LiteralType::ORDER, b.id, false, i-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);

        bool curr_elem = get_bool_from_array(as, i);

        new_clause1 = { make_literal(LiteralType::BOOL_VARIABLE, c.id, curr_elem ? true : false, 0), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);        

        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }
    
    cnf_clauses.push_back(helpers);
}

// Encodes a constraint of type r ↔ ⋁i as[i]
void Encoder::encode_array_bool_or(const ArrayLiteral& as, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    vector<shared_ptr<Literal>> new_clause1;
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    for(int i = 0; i < (int)as.size(); i++){
        auto p = get_var_from_array(as, i);
        shared_ptr<Literal> not_p = make_literal(LiteralType::BOOL_VARIABLE, p->id, false, 0);
        shared_ptr<Literal> yes_p = make_literal(LiteralType::BOOL_VARIABLE, p->id, true, 0); 

        new_clause1.push_back(yes_p);

        vector<shared_ptr<Literal>> new_clause2 = {not_p, yes_r};
        cnf_clauses.push_back(new_clause2);

    }

    new_clause1.push_back(not_r);
    cnf_clauses.push_back(new_clause1);

}

// Encodes a constraint of type xor i as[i]
void Encoder::encode_array_bool_xor(const ArrayLiteral& as, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    

    auto var0 = get_var_from_array(as, 0);
    auto var1 = get_var_from_array(as, 1);
    if(as.size() == 2){
        encode_bool_xor(*var0, *var1, cnf_clauses);
        return;
    }

    shared_ptr<Literal> yes_var0 = make_literal(LiteralType::BOOL_VARIABLE, var0->id, true, 0);
    shared_ptr<Literal> yes_var1 = make_literal(LiteralType::BOOL_VARIABLE, var1->id, true, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
    shared_ptr<Literal> not_var0 = make_literal(LiteralType::BOOL_VARIABLE, var0->id, false, 0);
    shared_ptr<Literal> not_var1 = make_literal(LiteralType::BOOL_VARIABLE, var1->id, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

    cnf_clauses.push_back({not_r, yes_var0, yes_var1});
    cnf_clauses.push_back({not_r, not_var0, not_var1});
    cnf_clauses.push_back({yes_r, not_var0, yes_var1});
    cnf_clauses.push_back({yes_r, yes_var0, not_var1});

    for(int i = 2; i < (int)as.size() - 1; i++){
        auto var_i = get_var_from_array(as, i);
        shared_ptr<Literal> yes_var_i = make_literal(LiteralType::BOOL_VARIABLE, var_i->id, true, 0);
        shared_ptr<Literal> yes_r0 = make_literal(LiteralType::HELPER, next_helper_id-1, true, 0);
        shared_ptr<Literal> yes_r1 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_var_i = make_literal(LiteralType::BOOL_VARIABLE, var_i->id, false, 0);
        shared_ptr<Literal> not_r0 = make_literal(LiteralType::HELPER, next_helper_id-1, false, 0);
        shared_ptr<Literal> not_r1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    
        cnf_clauses.push_back({not_r1, yes_var_i, yes_r0});
        cnf_clauses.push_back({not_r1, not_var_i, not_r0});
        cnf_clauses.push_back({yes_r1, not_var_i, yes_r0});
        cnf_clauses.push_back({yes_r1, yes_var_i, not_r0});
        
    }

    auto var_n = get_var_from_array(as, as.size() - 1);
    shared_ptr<Literal> yes_var_n = make_literal(LiteralType::BOOL_VARIABLE, var_n->id, true, 0);
    shared_ptr<Literal> yes_r_n = make_literal(LiteralType::HELPER, next_helper_id-1, true, 0);
    shared_ptr<Literal> not_var_n = make_literal(LiteralType::BOOL_VARIABLE, var_n->id, false, 0);
    shared_ptr<Literal> not_r_n = make_literal(LiteralType::HELPER, next_helper_id-1, false, 0);

    cnf_clauses.push_back({yes_var_n, yes_r_n});
    cnf_clauses.push_back({not_var_n, not_r_n});
}

// Encodes a constraint of type as[b] = c, where as is an array of bool var parameters
void Encoder::encode_array_var_bool_element(const BasicVar& b, const ArrayLiteral& as, BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int b_left = get_left(&b);
    int b_right = get_right(&b);
    
    vector<shared_ptr<Literal>> helpers;  
    vector<shared_ptr<Literal>> new_clause1, new_clause2;
    for(int i = b_left; i <= b_right; i++){
        if(i < 0 || i >= (int)as.size())
            continue;
        
        shared_ptr<Literal> helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        new_clause1 = { make_literal(LiteralType::ORDER, b.id, true, i), helper};
        new_clause2 = { make_literal(LiteralType::ORDER, b.id, false, i-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);

        auto curr_elem = get_var_from_array(as, i);

        new_clause1 = { make_literal(LiteralType::BOOL_VARIABLE, c.id, true, 0),
                        make_literal(LiteralType::BOOL_VARIABLE, curr_elem->id, false, 0),
                         helper};
        new_clause2 = { make_literal(LiteralType::BOOL_VARIABLE, c.id, false, 0),
                        make_literal(LiteralType::BOOL_VARIABLE, curr_elem->id, true, 0),
                        helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);        

        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }
    
    cnf_clauses.push_back(helpers);
}

void Encoder::encode_bool2int(const BasicVar& a, const BasicVar& b, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    
    if(b_left > 1 || b_right < 0){
        declare_unsat();
        return;
    }

    if(b_left == 1){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, 1)});

        return;
    }

    if(b_right == 0){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1)});
        
        return;
    }

    shared_ptr<Literal> yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
    shared_ptr<Literal> not_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    shared_ptr<Literal> yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
    shared_ptr<Literal> not_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

    cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, 0),
                            not_helper1});
    cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1),
                            not_helper1});
    cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0),
                            not_helper1});
 
    cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, 1),
                            not_helper2});
    cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, 0),
                            not_helper2});
    cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0),
                            not_helper2});         

    cnf_clauses.push_back({yes_helper1, yes_helper2});

}


// Encodes a constraint of type a /\ b <=> r
void Encoder::encode_bool_and(const BasicVar& a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, yes_a});
    cnf_clauses.push_back({not_r, yes_b});
    cnf_clauses.push_back({yes_r, not_a, not_b});
}

// Encodes a constraint of type ⋁i as[i] ∨ ⋁j ¬bs[j]
void Encoder::encode_bool_clause(const ArrayLiteral& as, const ArrayLiteral &bs, vector<vector<shared_ptr<Literal>>>& cnf_clauses){
    
    vector<shared_ptr<Literal>> new_clause;
    
    for(int i = 0; i < (int)as.size(); i++){
        auto var = get_var_from_array(as, i);
        shared_ptr<Literal> l = make_literal(LiteralType::BOOL_VARIABLE, var->id, true, 0);
        new_clause.push_back(l);
    }

    for(int j = 0; j < (int)bs.size(); j++){
        auto var = get_var_from_array(bs, j);
        shared_ptr<Literal> l = make_literal(LiteralType::BOOL_VARIABLE, var->id, false, 0);
        new_clause.push_back(l);
    }    

    cnf_clauses.push_back(new_clause);
}

// Encodes constraint of type a = b
void Encoder::encode_bool_eq(const BasicVar &a, const BasicVar& b, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);

    cnf_clauses.push_back({yes_a, not_b});
    cnf_clauses.push_back({not_a, yes_b});
}

// Encodes a constraint of type a = b <=> r
void Encoder::encode_bool_eq_reif(const BasicVar &a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({yes_r, not_a, not_b});
    cnf_clauses.push_back({yes_r, yes_a, yes_b});
    cnf_clauses.push_back({not_r, yes_a, not_b});
    cnf_clauses.push_back({not_r, not_a, yes_b});
}

// Encodes a constraint of type r => a = b
void Encoder::encode_bool_eq_imp(const BasicVar &a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, yes_a, not_b});
    cnf_clauses.push_back({not_r, not_a, yes_b});
}

// Encodes constraint of type a <= b
void Encoder::encode_bool_le(const BasicVar &a, const BasicVar& b, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);

    cnf_clauses.push_back({yes_b, not_a});
}

// Encodes a constraint of type a <= b <=> r
void Encoder::encode_bool_le_reif(const BasicVar &a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, not_a, yes_b});
    cnf_clauses.push_back({yes_r, yes_a});
    cnf_clauses.push_back({yes_r, not_b});
}

// Encodes a constraint of type r => a <= b
void Encoder::encode_bool_le_imp(const BasicVar &a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){

    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, not_a, yes_b});
}

// Encodes a substitution x = a1*x2 + a2*x2
void Encoder::encode_bool_substitution(const BasicVar &x, const BasicVar &x1, int coef1, const BasicVar &x2, int coef2, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int x_left = get_left(&x);
    int x_right = get_right(&x);
    int x1_left = get_left(&x1);
    int x1_right = get_right(&x1);
    int x2_left = get_left(&x2);
    int x2_right = get_right(&x2);

    encode_direct(x, cnf_clauses);
    if(!holds_alternative<BasicParType>(*x1.type))
        encode_direct(x1, cnf_clauses);

    //x = x1 + x2
    vector<shared_ptr<Literal>> helpers;
    for(int i = x_left; i <= x_right; i++){
        for(int j = x1_left; j <= x1_right; j++){
            for(int k = x2_left; k <= x2_right; k++){
                if(j*coef1 + k*coef2 == i){
                    shared_ptr<Literal> l_i = make_literal(LiteralType::DIRECT, x.id, true, i);
                    shared_ptr<Literal> l_j;
                    if(holds_alternative<BasicParType>(*x1.type))
                        l_j = make_literal(LiteralType::BOOL_VARIABLE, x1.id, j == 0 ? false : true, 0);
                    else    
                        l_j = make_literal(LiteralType::DIRECT, x1.id, true, j);
                    shared_ptr<Literal> l_k = make_literal(LiteralType::BOOL_VARIABLE, x2.id, k == 0 ? false : true, 0);

                    shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
                    shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

                    cnf_clauses.push_back({l_i, yes_helper});
                    cnf_clauses.push_back({l_j, yes_helper});
                    cnf_clauses.push_back({l_k, yes_helper});
                    helpers.push_back(not_helper);
                }   
                
            }
        }
    }    

    cnf_clauses.push_back(helpers);

}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn = c
void Encoder::encode_bool_lin_eq(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        if(coef > 0){
            sum2 += coef;
        } else {
            sum1 += coef;
        }
    }
    if(c < sum1 || c > sum2){
        declare_unsat();
        return ;
    }    

    if(vars.size() == 1){

        auto var = get_var_from_array(vars, 0);
        int coef = get_int_from_array(coefs, 0);
        if(c == 0)
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, var->id, false, 0)}); 
        else if(c == coef)
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, var->id, true, 0)});
        else
            declare_unsat();
        return;
    }

    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    int lower_bound1 = min({coef0, 0});
    int upper_bound1 = max({coef0, 0}); 
    int lower_bound2 = min({coef1, 0});
    int upper_bound2 = max({coef1, 0}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_bool_substitution(*var, *get_var_from_array(vars, 0), get_int_from_array(coefs, 0),
                        *get_var_from_array(vars, 1), get_int_from_array(coefs, 1), cnf_clauses);
    
    BasicVar* var1;
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

        encode_bool_substitution(*var1, *var, 1, *get_var_from_array(vars, i), get_int_from_array(coefs, i), cnf_clauses);

        var = var1;
    }

    if(vars.size() == 2){
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c - 1)});
    } else {
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, false, c - 1)});
    }
}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn <= c
void Encoder::encode_bool_lin_le(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        if(coef > 0){
            sum2 += coef;
        } else {
            sum1 += coef;
        }
    }
    if(c < sum1){
        declare_unsat();
        return ;
    } else if(c > sum2){
        return;
    }

    if(vars.size() == 1){

        auto var = get_var_from_array(vars, 0);
        int coef = get_int_from_array(coefs, 0);
        if(c == 0)
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, var->id, false, 0)}); 
        else if(c == coef)
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, var->id, true, 0)});
        else
            declare_unsat();
        return;
    }

    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    int lower_bound1 = min({coef0, 0});
    int upper_bound1 = max({coef0, 0}); 
    int lower_bound2 = min({coef1, 0});
    int upper_bound2 = max({coef1, 0}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_bool_substitution(*var, *get_var_from_array(vars, 0), get_int_from_array(coefs, 0),
                        *get_var_from_array(vars, 1), get_int_from_array(coefs, 1), cnf_clauses);
    
    BasicVar* var1;
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

        encode_bool_substitution(*var1, *var, 1, *get_var_from_array(vars, i), get_int_from_array(coefs, i), cnf_clauses);

        var = var1;
    }

    if(vars.size() == 2)
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c)});
    else
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c)});
}

// Encodes constraint of type a < b
void Encoder::encode_bool_lt(const BasicVar &a, const BasicVar& b, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);

    cnf_clauses.push_back({yes_b});
    cnf_clauses.push_back({not_a});
}

// Encodes a constraint of type a < b <=> r
void Encoder::encode_bool_lt_reif(const BasicVar &a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({yes_r, yes_a, not_b});
    cnf_clauses.push_back({not_r, not_a});
    cnf_clauses.push_back({not_r, yes_b});
}

// Encodes a constraint of type r => a < b
void Encoder::encode_bool_lt_imp(const BasicVar &a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){

    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, not_a});
    cnf_clauses.push_back({not_r, yes_b});
}

// Encodes constraint of type a =/= b
void Encoder::encode_bool_not(const BasicVar &a, const BasicVar& b, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);

    cnf_clauses.push_back({not_a, not_b});
    cnf_clauses.push_back({yes_a, yes_b});
}

// Encodes a constraint of type a \/ b <=> r
void Encoder::encode_bool_or(const BasicVar &a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({yes_r, not_a});
    cnf_clauses.push_back({yes_r, not_b});
    cnf_clauses.push_back({not_r, yes_a, yes_b});
}

// Encodes a constraint of type a xor b <=> r
void Encoder::encode_bool_xor(const BasicVar &a, const BasicVar& b, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, yes_a, yes_b});
    cnf_clauses.push_back({not_r, not_a, not_b});
    cnf_clauses.push_back({yes_r, not_a, yes_b});
    cnf_clauses.push_back({yes_r, yes_a, not_b});
}

// Encodes a constraint of type a xor b <=> true
void Encoder::encode_bool_xor(const BasicVar &a, const BasicVar& b, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    shared_ptr<Literal> yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    shared_ptr<Literal> yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    shared_ptr<Literal> not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    shared_ptr<Literal> not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);

    cnf_clauses.push_back({yes_a, yes_b});
    cnf_clauses.push_back({not_a, not_b});
}

// ---------------------------- Encoding Set constraints -------------------------------------

// Encodes a constraint of type as[b] = c
void Encoder::encode_array_set_element(const BasicVar& b, const ArrayLiteral& as, const BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int b_left = get_left(&b);
    int b_right = get_right(&b);

    vector<shared_ptr<Literal>> helpers;
    for(int i = b_left; i <= b_right; i++){
        if(i < 0 || i >= (int)as.size())
            continue;

        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        auto curr_var = *get_set_from_array(as, i);

        vector<int> elems;
        if(holds_alternative<SetSetLiteral*>(curr_var)){
            elems = *get<SetSetLiteral*>(curr_var)->elems;
        } else {
            int left = get<SetRangeLiteral*>(curr_var)->left;
            int right = get<SetRangeLiteral*>(curr_var)->right;
            for(int i = left; i <= right; i++)
                elems.push_back(i);
        }

        vector<vector<shared_ptr<Literal>>> temp_clauses;
        int j = 0, k = 0;
        auto cs = *get_set_elems(c);
    
        
        while(j < (int)elems.size() && k < (int)cs.size()){
            if(elems[j] < cs[k]){
                temp_clauses.push_back({not_helper});
                j++;
            } else if(elems[j] > cs[k]){
                temp_clauses.push_back({make_literal(LiteralType::SET_ELEM, c.id, false, cs[k])});
                k++;
            } else {
                shared_ptr<Literal> yes_c = make_literal(LiteralType::SET_ELEM, c.id, true, cs[k]);
            
                temp_clauses.push_back({yes_c});
                j++; k++;
            }
        }
    
        if(j < (int)elems.size()){
            temp_clauses.push_back({not_helper});
        }

        while(k < (int)cs.size())
            temp_clauses.push_back({make_literal(LiteralType::SET_ELEM, c.id, false, cs[k++])});
        
        for(auto clause : temp_clauses){
            clause.push_back(not_helper);
            cnf_clauses.push_back(clause);
        }

        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, i), not_helper});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, i - 1), not_helper});

        helpers.push_back(yes_helper);
    }

    cnf_clauses.push_back(helpers);
}

// Encodes a constraint of type as[b] = c
void Encoder::encode_array_var_set_element(const BasicVar& b, const ArrayLiteral& as, const BasicVar& c, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int b_left = get_left(&b);
    int b_right = get_right(&b);

    vector<shared_ptr<Literal>> helpers;
    for(int i = b_left; i <= b_right; i++){
        if(i < 0 || i >= (int)as.size())
            continue;

        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        auto curr_var = *get_var_from_array(as, i);

        vector<vector<shared_ptr<Literal>>> temp_clauses;
        encode_set_eq(curr_var, c, temp_clauses);
        for(auto clause : temp_clauses){
            clause.push_back(not_helper);
            cnf_clauses.push_back(clause);
        }

        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, i), not_helper});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, i - 1), not_helper});

        helpers.push_back(yes_helper);
    }

    cnf_clauses.push_back(helpers);
}

// Encodes a substitution x = a1*x2 + a2*x2
void Encoder::encode_set_substitution(const BasicVar &x, const BasicVar &x1, int val1, int val2, int S_id, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    int x_left = get_left(&x);
    int x_right = get_right(&x);
    int x1_left = get_left(&x1);
    int x1_right = get_right(&x1);
    if(x1.id == x.id){
        x1_left = 0;
        x1_right = 1;
    }

    encode_direct(x, cnf_clauses);
    if(x1.id != x.id)
        encode_direct(x1, cnf_clauses);

    //x = x1 + x2
    vector<shared_ptr<Literal>> helpers;
    for(int i = x_left; i <= x_right; i++){
        for(int j = x1_left; j <= x1_right; j++){
            for(int k = 0; k <= 1; k++){
                if(j + k == i){
                    shared_ptr<Literal> l_i = make_literal(LiteralType::DIRECT, x.id, true, i);
                    shared_ptr<Literal> l_j;
                    if(x.id == x1.id)
                        l_j = make_literal(LiteralType::SET_ELEM, S_id, j == 0 ? false : true, val1);
                    else    
                        l_j = make_literal(LiteralType::DIRECT, x1.id, true, j);
                    shared_ptr<Literal> l_k = make_literal(LiteralType::SET_ELEM, S_id, k == 0 ? false : true, val2);

                    shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
                    shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

                    cnf_clauses.push_back({l_i, yes_helper});
                    cnf_clauses.push_back({l_j, yes_helper});
                    cnf_clauses.push_back({l_k, yes_helper});
                    helpers.push_back(not_helper);
                }   
                
            }
        }
    }    

    cnf_clauses.push_back(helpers);

}

// Encodes a constraint of type |S| = x
void Encoder::encode_set_card(const BasicVar& S, int x, int x_id, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    auto elems = *get_set_elems(S);

    if(x > (int)elems.size() || x < 0){
        cnf_clauses.push_back({});
        return;
    }

    if(elems.size() == 1){
        if(x == 0){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, false, elems[0])});    
            return;
        }
        if(x != 1){
            cnf_clauses.push_back({});
            return;  
        }
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, x_id, false, 0),
                               make_literal(LiteralType::SET_ELEM, S.id, false, elems[0])});

        cnf_clauses.push_back({make_literal(LiteralType::ORDER, x_id, true, 1),
                               make_literal(LiteralType::SET_ELEM, S.id, false, elems[0])}); 

        cnf_clauses.push_back({make_literal(LiteralType::ORDER, x_id, true, 0),
                               make_literal(LiteralType::ORDER, x_id, false, 1), 
                               make_literal(LiteralType::SET_ELEM, S.id, true, elems[0])});
        return;
    }

    int lower_bound = 0;
    int upper_bound = 2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_set_substitution(*var, *var, elems[0], elems[1], S.id, cnf_clauses);
    
    BasicVar* var1;
    for(int i = 2; i < (int)elems.size(); i++){
 
        lower_bound = 0;
        upper_bound = i + 1;


        var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);

        encode_set_substitution(*var1, *var, 1, elems[i], S.id, cnf_clauses);

        var = var1;
    }

    if(elems.size() == 2){
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, x)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, x - 1)});
    } else {
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, x)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, false, x - 1)});
    }
}

// Encodes a constraint of type |S| = x
void Encoder::encode_set_card(const BasicVar& S, const BasicVar& x, vector<vector<shared_ptr<Literal>>>& cnf_clauses){

    auto elems = get_set_elems(S);
    int left = get_left(&x);
    int right = get_right(&x);

    if(left > (int)elems->size() || right < 0){
        declare_unsat();
        return;
    }

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    vector<shared_ptr<Literal>> helpers;
    for(int i = left; i <= right; i++){
        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        encode_set_card(S, i, x.id, temp_clauses);

        for(auto clause : temp_clauses){
            clause.push_back(not_helper);
            cnf_clauses.push_back(clause);
        }

        cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, i), not_helper});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, i - 1), not_helper});


        helpers.push_back(yes_helper);
        temp_clauses.clear();
    }

    cnf_clauses.push_back(helpers);
}

// Encodes a constraint of type r = x \ y
void Encoder::encode_set_diff(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    auto rs = *get_set_elems(r);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            cnf_clauses.push_back({yes_x, not_r});
            cnf_clauses.push_back({not_x, yes_r});            
            i++;
        } else if(xs[i] > ys[j]){
            j++;
        } else {
            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, xs[i]);
            shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, xs[i]);
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            cnf_clauses.push_back({not_r, yes_x});
            cnf_clauses.push_back({not_r, not_y});
            cnf_clauses.push_back({yes_r, not_x, yes_y}); 
            i++; j++;
        }
    }

    while(i < (int)xs.size()){
        shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
        shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
        shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
        shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);

        cnf_clauses.push_back({yes_x, not_r});
        cnf_clauses.push_back({not_x, yes_r});            
        i++;
    }

}

// Encodes a constraint of type x = y
void Encoder::encode_set_eq(const BasicVar& x, const BasicVar& y, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i])});
            i++;
        } else if(xs[i] > ys[j]){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, y.id, false, ys[j])});
            j++;
        } else {
            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);
        
            cnf_clauses.push_back({yes_x, not_y});
            cnf_clauses.push_back({not_x, yes_y});          
            i++; j++;
        }
    }

    while(i < (int)xs.size())
        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i++])});

    while(j < (int)ys.size())
        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, y.id, false, ys[j++])});
    
}

// Encodes a constraint of type (x = y) <=> r
void Encoder::encode_set_eq_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    encode_set_eq(x, y, temp_clauses);

    reify(temp_clauses, r, cnf_clauses);
}

// Encodes a constraint of type r => (x = y)
void Encoder::encode_set_eq_imp(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    encode_set_eq(x, y, temp_clauses);

    impify(temp_clauses, r, cnf_clauses);
}

// Encodes a constraint of type x ∈ y
void Encoder::encode_set_in(const BasicVar& x, const BasicVar& S, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    
    auto elems = *get_set_elems(S);
    auto left = get_left(&x);
    auto right = get_right(&x);

    if(left > elems[elems.size() - 1] || right < elems[0]){
        declare_unsat();
        return ;
    }

    vector<shared_ptr<Literal>> helpers;
    for(auto elem : elems){
        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        if(elem >= left && elem <= right){
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, elem),
                                    not_helper});
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, elem-1),
                                    not_helper});
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, true, elem),
                                    not_helper});
        helpers.push_back(yes_helper);
        }
    }

    cnf_clauses.push_back(helpers);
}

// Encodes a constraint of type (x ∈ S) <=> r, where S is a set parameter
void Encoder::encode_set_in_reif(const BasicVar& x, const BasicLiteralExpr& S1, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    
    auto S = get<SetLiteral*>(S1);
    auto left = get_left(&x);
    auto right = get_right(&x);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

    vector<int> elems;
    if(holds_alternative<SetSetLiteral*>(*S)){
        elems = *get<SetSetLiteral*>(*S)->elems;
    } else {
        int left = get<SetRangeLiteral*>(*S)->left;
        int right = get<SetRangeLiteral*>(*S)->right;
        for(int i = left; i <= right; i++)
            elems.push_back(i);
    }

    if(left > elems[elems.size() - 1] || right < elems[0]){
        cnf_clauses.push_back({not_r});
        return ;
    }

    vector<shared_ptr<Literal>> helpers;
    for(auto elem : elems){
        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        if(elem >= left && elem <= right){    
            
            vector<shared_ptr<Literal>> new_clause1;

            shared_ptr<Literal> not_p1 = make_literal(LiteralType::ORDER, x.id, false, elem);
            shared_ptr<Literal> yes_p1 = make_literal(LiteralType::ORDER, x.id, true, elem); 
            shared_ptr<Literal> not_p2 = make_literal(LiteralType::ORDER, x.id, true, elem-1);
            shared_ptr<Literal> yes_p2 = make_literal(LiteralType::ORDER, x.id, false, elem-1); 
            
            new_clause1.push_back(not_p1);
            new_clause1.push_back(not_p2);

            vector<shared_ptr<Literal>> new_clause2 = {yes_p1, not_helper};
            cnf_clauses.push_back(new_clause2);
            new_clause2 = {yes_p2, not_helper};
            cnf_clauses.push_back(new_clause2);

            new_clause1.push_back(yes_helper);
            cnf_clauses.push_back(new_clause1);
            
            helpers.push_back(yes_helper);
        }
    }

    vector<shared_ptr<Literal>> new_clause1;

    for(int i = 0; i < (int)helpers.size(); i++){
        shared_ptr<Literal> yes_p = helpers[i];
        shared_ptr<Literal> not_p = make_literal(LiteralType::HELPER, yes_p->id, false, 0);

        new_clause1.push_back(yes_p);

        vector<shared_ptr<Literal>> new_clause2 = {not_p, yes_r};
        cnf_clauses.push_back(new_clause2);

    }

    new_clause1.push_back(not_r);
    cnf_clauses.push_back(new_clause1);
}

// Encodes a constraint of type (x ∈ S) <=> r, where S is a set variable
void Encoder::encode_set_in_reif(const BasicVar& x, const BasicVar& S, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    
    auto elems = *get_set_elems(S);
    auto left = get_left(&x);
    auto right = get_right(&x);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

    if(left > elems[elems.size() - 1] || right < elems[0]){
        cnf_clauses.push_back({not_r});
        return ;
    }

    vector<shared_ptr<Literal>> helpers;
    for(auto elem : elems){
        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        if(elem >= left && elem <= right){    
            vector<shared_ptr<Literal>> new_clause1;

            shared_ptr<Literal> not_p1 = make_literal(LiteralType::ORDER, x.id, false, elem);
            shared_ptr<Literal> yes_p1 = make_literal(LiteralType::ORDER, x.id, true, elem); 
            shared_ptr<Literal> not_p2 = make_literal(LiteralType::ORDER, x.id, true, elem-1);
            shared_ptr<Literal> yes_p2 = make_literal(LiteralType::ORDER, x.id, false, elem-1); 
            shared_ptr<Literal> not_p3 = make_literal(LiteralType::SET_ELEM, S.id, false, elem);
            shared_ptr<Literal> yes_p3 = make_literal(LiteralType::SET_ELEM, S.id, true, elem); 
                
            new_clause1.push_back(not_p1);
            new_clause1.push_back(not_p2);
            new_clause1.push_back(not_p3);
        
            vector<shared_ptr<Literal>> new_clause2 = {yes_p1, not_helper};
            cnf_clauses.push_back(new_clause2);
            new_clause2 = {yes_p2, not_helper};
            cnf_clauses.push_back(new_clause2);
            new_clause2 = {yes_p3, not_helper};
            cnf_clauses.push_back(new_clause2);
        
            new_clause1.push_back(yes_helper);
            cnf_clauses.push_back(new_clause1);
            
            helpers.push_back(yes_helper);
        }
    }

    vector<shared_ptr<Literal>> new_clause1;

    for(int i = 0; i < (int)helpers.size(); i++){
        shared_ptr<Literal> yes_p = helpers[i];
        shared_ptr<Literal> not_p = make_literal(LiteralType::HELPER, yes_p->id, false, 0);

        new_clause1.push_back(yes_p);

        vector<shared_ptr<Literal>> new_clause2 = {not_p, yes_r};
        cnf_clauses.push_back(new_clause2);

    }

    new_clause1.push_back(not_r);
    cnf_clauses.push_back(new_clause1);
}

// Encodes a constraint of type (x ∈ S) => r, where S is a set parameter
void Encoder::encode_set_in_imp(const BasicVar& x, const BasicLiteralExpr& S1, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    
    auto S = get<SetLiteral*>(S1);
    auto left = get_left(&x);
    auto right = get_right(&x);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    vector<int> elems;
    if(holds_alternative<SetSetLiteral*>(*S)){
        elems = *get<SetSetLiteral*>(*S)->elems;
    } else {
        int left = get<SetRangeLiteral*>(*S)->left;
        int right = get<SetRangeLiteral*>(*S)->right;
        for(int i = left; i <= right; i++)
            elems.push_back(i);
    }

    if(left > elems[elems.size() - 1] || right < elems[0]){
        cnf_clauses.push_back({not_r});
        return ;
    }

    vector<shared_ptr<Literal>> helpers;
    for(auto elem : elems){
        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        if(elem >= left && elem <= right){    
            
            vector<shared_ptr<Literal>> new_clause1;

            shared_ptr<Literal> not_p1 = make_literal(LiteralType::ORDER, x.id, false, elem);
            shared_ptr<Literal> yes_p1 = make_literal(LiteralType::ORDER, x.id, true, elem); 
            shared_ptr<Literal> not_p2 = make_literal(LiteralType::ORDER, x.id, true, elem-1);
            shared_ptr<Literal> yes_p2 = make_literal(LiteralType::ORDER, x.id, false, elem-1); 
            
            new_clause1.push_back(not_p1);
            new_clause1.push_back(not_p2);

            vector<shared_ptr<Literal>> new_clause2 = {yes_p1, not_helper};
            cnf_clauses.push_back(new_clause2);
            new_clause2 = {yes_p2, not_helper};
            cnf_clauses.push_back(new_clause2);

            new_clause1.push_back(yes_helper);
            cnf_clauses.push_back(new_clause1);
            
            helpers.push_back(yes_helper);
        }
    }

    helpers.push_back(not_r);
    cnf_clauses.push_back(helpers);
}

// Encodes a constraint of type r => (x ∈ S), where S is a set variable
void Encoder::encode_set_in_imp(const BasicVar& x, const BasicVar& S, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    
    auto elems = *get_set_elems(S);
    auto left = get_left(&x);
    auto right = get_right(&x);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    if(left > elems[elems.size() - 1] || right < elems[0]){
        cnf_clauses.push_back({not_r});
        return ;
    }

    vector<shared_ptr<Literal>> helpers;
    for(auto elem : elems){
        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        if(elem >= left && elem <= right){    
            vector<shared_ptr<Literal>> new_clause1;

            shared_ptr<Literal> not_p1 = make_literal(LiteralType::ORDER, x.id, false, elem);
            shared_ptr<Literal> yes_p1 = make_literal(LiteralType::ORDER, x.id, true, elem); 
            shared_ptr<Literal> not_p2 = make_literal(LiteralType::ORDER, x.id, true, elem-1);
            shared_ptr<Literal> yes_p2 = make_literal(LiteralType::ORDER, x.id, false, elem-1); 
            shared_ptr<Literal> not_p3 = make_literal(LiteralType::SET_ELEM, S.id, false, elem);
            shared_ptr<Literal> yes_p3 = make_literal(LiteralType::SET_ELEM, S.id, true, elem); 
                
            new_clause1.push_back(not_p1);
            new_clause1.push_back(not_p2);
            new_clause1.push_back(not_p3);
        
            vector<shared_ptr<Literal>> new_clause2 = {yes_p1, not_helper};
            cnf_clauses.push_back(new_clause2);
            new_clause2 = {yes_p2, not_helper};
            cnf_clauses.push_back(new_clause2);
            new_clause2 = {yes_p3, not_helper};
            cnf_clauses.push_back(new_clause2);
        
            new_clause1.push_back(yes_helper);
            cnf_clauses.push_back(new_clause1);
            
            helpers.push_back(yes_helper);
        }
    }

    helpers.push_back(not_r);
    cnf_clauses.push_back(helpers);
}

// Encodes a constraint of type x =/= y
void Encoder::encode_set_ne(const BasicVar& x, const BasicVar& y, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);

    vector<shared_ptr<Literal>> helpers;
    while(i < (int)xs.size() && j < (int)ys.size()){

        if(xs[i] < ys[j]){
            helpers.push_back(make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]));
            i++;
        } else if(xs[i] > ys[j]){
            helpers.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, ys[i]));
            j++;
        } else {

            shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
            shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);

            cnf_clauses.push_back({yes_x, yes_y, not_helper});
            cnf_clauses.push_back({not_x, not_y, not_helper});
            helpers.push_back(yes_helper);          
            i++; j++;
        }
    }


    while(i < (int)xs.size())
        helpers.push_back(make_literal(LiteralType::SET_ELEM, x.id, true, xs[i++]));

    
    while(j < (int)ys.size())
        helpers.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, ys[j++]));
    

    cnf_clauses.push_back(helpers);
}

// Encodes a constraint of type (x =/= y) <=> r
void Encoder::encode_set_ne_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r,vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    shared_ptr<Literal> yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

    vector<shared_ptr<Literal>> helpers;
    while(i < (int)xs.size() && j < (int)ys.size()){

        if(xs[i] < ys[j]){
            helpers.push_back(make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]));
            i++;
        } else if(xs[i] > ys[j]){
            helpers.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, ys[i]));
            j++;
        } else {

            shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
            shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);

            cnf_clauses.push_back({yes_x, yes_y, not_helper});
            cnf_clauses.push_back({not_x, not_y, not_helper});
            cnf_clauses.push_back({yes_x, not_y, yes_helper});
            cnf_clauses.push_back({not_x, yes_y, yes_helper});
            helpers.push_back(yes_helper);          
            i++; j++;
        }
    }

    while(i < (int)xs.size())
        helpers.push_back(make_literal(LiteralType::SET_ELEM, x.id, true, xs[i++]));

    while(j < (int)ys.size())
        helpers.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, ys[j++]));

    vector<shared_ptr<Literal>> new_clause1;

    for(int i = 0; i < (int)helpers.size(); i++){
        shared_ptr<Literal> yes_p = helpers[i];
        shared_ptr<Literal> not_p = make_literal(yes_p->type, yes_p->id, false, yes_p->val);

        new_clause1.push_back(yes_p);

        vector<shared_ptr<Literal>> new_clause2 = {not_p, yes_r};
        cnf_clauses.push_back(new_clause2);

    }

    new_clause1.push_back(not_r);
    cnf_clauses.push_back(new_clause1);
}

// Encodes a constraint of type r => (x =/= y)
void Encoder::encode_set_ne_imp(const BasicVar& x, const BasicVar& y, const BasicVar& r,vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    shared_ptr<Literal> not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    vector<shared_ptr<Literal>> helpers;
    while(i < (int)xs.size() && j < (int)ys.size()){
        shared_ptr<Literal> yes_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        if(xs[i] < ys[j]){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]), not_helper});
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]), yes_helper});
            helpers.push_back(yes_helper);
            i++;
        } else if(xs[i] > ys[j]){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, y.id, true, ys[i]), not_helper});
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, y.id, false, ys[i]), yes_helper});
            helpers.push_back(yes_helper);
            j++;
        } else {
            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);

            cnf_clauses.push_back({yes_x, yes_y, not_helper});
            cnf_clauses.push_back({not_x, not_y, not_helper});
            cnf_clauses.push_back({yes_x, not_y, yes_helper});
            cnf_clauses.push_back({not_x, yes_y, yes_helper});
            helpers.push_back(yes_helper);          
            i++; j++;
        }
    }

    helpers.push_back(not_r);
    cnf_clauses.push_back(helpers);
}

// Encodes a constraint of type r = x ∩ y
void Encoder::encode_set_intersect(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    auto rs = *get_set_elems(r);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            cnf_clauses.push_back({not_r});            
            i++;
        } else if(xs[i] > ys[j]){
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
        
            cnf_clauses.push_back({not_r});    
            j++;
        } else {
            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, xs[i]);
            shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, xs[i]);
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            cnf_clauses.push_back({not_r, yes_x});
            cnf_clauses.push_back({not_r, yes_y});
            cnf_clauses.push_back({yes_r, not_x, not_y});
            i++; j++;
        }
    }

    while(i < (int)xs.size()){
        shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
        cnf_clauses.push_back({not_r});              
        i++;
    }

    while(j < (int)ys.size()){
        shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
        
        cnf_clauses.push_back({not_r});    
        j++;
    }
}

void Encoder::set_max(const BasicVar& x, const BasicVar& set, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    auto elems = *get_set_elems(set);

    vector<shared_ptr<Literal>> empty_set_clause;

    vector<shared_ptr<Literal>> helpers;
    for(auto elem : elems){
        auto yes_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        auto not_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, set.id, false, elem), 
                               make_literal(LiteralType::ORDER, x.id, false, elem-1)});  
                               
        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, set.id, false, elem), 
                               make_literal(LiteralType::ORDER, x.id, true, elem), not_helper}); 
        helpers.push_back(yes_helper);

        empty_set_clause.push_back(make_literal(LiteralType::SET_ELEM, set.id, true, elem));
    }

    empty_set_clause.push_back(make_literal(LiteralType::ORDER, x.id, true, elems[0]-1));
    cnf_clauses.push_back(helpers);
    cnf_clauses.push_back(empty_set_clause);
}

// Encodes a constraint of type x <= y
void Encoder::encode_set_le(const BasicVar& x, const BasicVar& y, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    auto x_elems = *get_set_elems(x);
    auto y_elems = *get_set_elems(y);
    int n = x_elems.size();
    int m = y_elems.size();

    if(x_elems.size() == 0)
        return;
    if(y_elems.size() == 0){
        declare_unsat();
        return;
    }

    int l = x_elems[0] < y_elems[0] ? x_elems[0] : y_elems[0];
    int u = x_elems[n-1] > y_elems[m-1] ? x_elems[n-1] : y_elems[m-1];

    auto xmax = encode_int_range_helper_variable(l-1, u, cnf_clauses);
    auto ymax = encode_int_range_helper_variable(l-1, u, cnf_clauses);

    set_max(*xmax, x, cnf_clauses);
    set_max(*ymax, y, cnf_clauses);

    int helper_x_id = next_helper_id++;
    int helper_y_id = next_helper_id++;

    for(int i = l; i <= u; i++){
        bool x_found = false;
        bool y_found = false;

        for(auto x_elem : x_elems){
            if(x_elem == i){
                x_found = true;
                break;
            } 
        }

        for(auto y_elem : y_elems){
            if(y_elem == i){
                y_found = true;
                break;
            } 
        }

        if(x_found){
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                                   make_literal(LiteralType::SET_ELEM, x.id, false, i)});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                                   make_literal(LiteralType::SET_ELEM, x.id, true, i)});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i)});
        }

        if(y_found){
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, true, i),
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, false, i),
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, false, i)});
        }
    }

    int helper_id = next_helper_id++; 

    for(int i = l; i < u; i++){
        shared_ptr<Literal> yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper3 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper3 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                               make_literal(LiteralType::HELPER, helper_y_id, false, i),
                               not_helper1});
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                               make_literal(LiteralType::HELPER, helper_y_id, true, i),
                               not_helper1});                           
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                               not_helper2});
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i+1),
                               not_helper2});
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                               not_helper3});
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i+1),
                               not_helper3});
                               
        cnf_clauses.push_back({yes_helper1, yes_helper2, yes_helper3});

        shared_ptr<Literal> yes_helper4 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper4 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper5 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper5 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                               not_helper4});     
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, ymax->id, false, i),
                               not_helper4});                         
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                               not_helper5});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, ymax->id, true, i),
                               not_helper5});

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                               make_literal(LiteralType::HELPER, helper_y_id, true, i),
                               yes_helper4, yes_helper5});

        shared_ptr<Literal> yes_helper6 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper6 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper7 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper7 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);


        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                               not_helper6});    
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, xmax->id, true, i-1),
                               not_helper6});                        
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                               not_helper7});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, xmax->id, false, i-1),
                               not_helper7});

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                               make_literal(LiteralType::HELPER, helper_y_id, false, i),
                               yes_helper6, yes_helper7});

    }

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, u),
                           make_literal(LiteralType::HELPER, helper_x_id, false, u),
                           make_literal(LiteralType::HELPER, helper_y_id, true, u)});

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, u),
                           make_literal(LiteralType::HELPER, helper_x_id, true, u)});

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, u),
                           make_literal(LiteralType::HELPER, helper_y_id, false, u)});

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, l)});
}

// Encodes a constraint of type (x <= y) <=> r
void Encoder::encode_set_le_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    auto x_elems = *get_set_elems(x);
    auto y_elems = *get_set_elems(y);
    int n = x_elems.size();
    int m = y_elems.size();

    if(x_elems.size() == 0)
        return;
    if(y_elems.size() == 0){
        declare_unsat();
        return;
    }

    int l = x_elems[0] < y_elems[0] ? x_elems[0] : y_elems[0];
    int u = x_elems[n-1] > y_elems[m-1] ? x_elems[n-1] : y_elems[m-1];

    auto xmax = encode_int_range_helper_variable(l-1, u, cnf_clauses);
    auto ymax = encode_int_range_helper_variable(l-1, u, cnf_clauses);

    set_max(*xmax, x, cnf_clauses);
    set_max(*ymax, y, cnf_clauses);

    int helper_x_id = next_helper_id++;
    int helper_y_id = next_helper_id++;

    for(int i = l; i <= u; i++){
        bool x_found = false;
        bool y_found = false;

        for(auto x_elem : x_elems){
            if(x_elem == i){
                x_found = true;
                break;
            } 
        }

        for(auto y_elem : y_elems){
            if(y_elem == i){
                y_found = true;
                break;
            } 
        }

        if(x_found){
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                                   make_literal(LiteralType::SET_ELEM, x.id, false, i)});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                                   make_literal(LiteralType::SET_ELEM, x.id, true, i)});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i)});
        }

        if(y_found){
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, true, i),
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, false, i),
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, false, i)});
        }
    }

    int helper_id = next_helper_id++; 

    for(int i = l; i < u; i++){
        shared_ptr<Literal> yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper3 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper3 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                               make_literal(LiteralType::HELPER, helper_y_id, false, i),
                               not_helper1});
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                               make_literal(LiteralType::HELPER, helper_y_id, true, i),
                               not_helper1});                           
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                               not_helper2});
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i+1),
                               not_helper2});
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                               not_helper3});
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i+1),
                               not_helper3});
                               
        cnf_clauses.push_back({yes_helper1, yes_helper2, yes_helper3});

        shared_ptr<Literal> yes_helper4 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper4 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper5 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper5 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                               not_helper4});     
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, ymax->id, false, i),
                               not_helper4});                         
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                               not_helper5});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, ymax->id, true, i),
                               not_helper5});

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                               make_literal(LiteralType::HELPER, helper_y_id, true, i),
                               yes_helper4, yes_helper5});

        shared_ptr<Literal> yes_helper6 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper6 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper7 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper7 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);


        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                               not_helper6});    
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, xmax->id, true, i-1),
                               not_helper6});                        
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                               not_helper7});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, xmax->id, false, i-1),
                               not_helper7});

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                               make_literal(LiteralType::HELPER, helper_y_id, false, i),
                               yes_helper6, yes_helper7});

    }

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, u),
                           make_literal(LiteralType::HELPER, helper_x_id, false, u),
                           make_literal(LiteralType::HELPER, helper_y_id, true, u)});

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, u),
                           make_literal(LiteralType::HELPER, helper_x_id, true, u)});

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, u),
                           make_literal(LiteralType::HELPER, helper_y_id, false, u)});

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, l),
                           make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, l),
                           make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
}

// Encodes a constraint of type x < y
void Encoder::encode_set_lt(const BasicVar& x, const BasicVar& y, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    auto x_elems = *get_set_elems(x);
    auto y_elems = *get_set_elems(y);
    int n = x_elems.size();
    int m = y_elems.size();

    if(y_elems.size() == 0){
        declare_unsat();
        return;
    }
    if(x_elems.size() == 0){
        vector<shared_ptr<Literal>> new_clause;
        for(auto elem : y_elems){
            new_clause.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, elem));
        }
        cnf_clauses.push_back(new_clause);

        return;
    }


    int l = x_elems[0] < y_elems[0] ? x_elems[0] : y_elems[0];
    int u = x_elems[n-1] > y_elems[m-1] ? x_elems[n-1] : y_elems[m-1];

    auto xmax = encode_int_range_helper_variable(l-1, u, cnf_clauses);
    auto ymax = encode_int_range_helper_variable(l-1, u, cnf_clauses);

    set_max(*xmax, x, cnf_clauses);
    set_max(*ymax, y, cnf_clauses);

    int helper_x_id = next_helper_id++;
    int helper_y_id = next_helper_id++;

    for(int i = l; i <= u; i++){
        bool x_found = false;
        bool y_found = false;

        for(auto x_elem : x_elems){
            if(x_elem == i){
                x_found = true;
                break;
            } 
        }

        for(auto y_elem : y_elems){
            if(y_elem == i){
                y_found = true;
                break;
            } 
        }

        if(x_found){
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                                   make_literal(LiteralType::SET_ELEM, x.id, false, i)});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                                   make_literal(LiteralType::SET_ELEM, x.id, true, i)});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i)});
        }

        if(y_found){
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, true, i),
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, false, i),
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, false, i)});
        }
    }

    int helper_id = next_helper_id++; 

    for(int i = l; i <= u; i++){
        shared_ptr<Literal> yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper3 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper3 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                            make_literal(LiteralType::HELPER, helper_y_id, false, i),
                            not_helper1});
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                            make_literal(LiteralType::HELPER, helper_y_id, true, i),
                            not_helper1});                           
        if(i != u){
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                                not_helper2});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i+1),
                                not_helper2});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                                not_helper3});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i+1),
                                not_helper3});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                                not_helper2});
            cnf_clauses.push_back({not_helper3});
        }
                               
        cnf_clauses.push_back({yes_helper1, yes_helper2, yes_helper3});

        shared_ptr<Literal> yes_helper4 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper4 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper5 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper5 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                               not_helper4});     
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, ymax->id, false, i),
                               not_helper4});                         
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                               not_helper5});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, ymax->id, true, i),
                               not_helper5});

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                               make_literal(LiteralType::HELPER, helper_y_id, true, i),
                               yes_helper4, yes_helper5});

        shared_ptr<Literal> yes_helper6 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper6 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper7 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper7 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);


        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                               not_helper6});    
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, xmax->id, true, i-1),
                               not_helper6});                        
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                               not_helper7});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, xmax->id, false, i-1),
                               not_helper7});

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                               make_literal(LiteralType::HELPER, helper_y_id, false, i),
                               yes_helper6, yes_helper7});

    }

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, l)});
}

// Encodes a constraint of type (x < y) <=> r
void Encoder::encode_set_lt_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    auto x_elems = *get_set_elems(x);
    auto y_elems = *get_set_elems(y);
    int n = x_elems.size();
    int m = y_elems.size();

    if(y_elems.size() == 0){
        declare_unsat();
        return;
    }
    if(x_elems.size() == 0){
        vector<shared_ptr<Literal>> new_clause;
        for(auto elem : y_elems){
            new_clause.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, elem));
        }
        cnf_clauses.push_back(new_clause);

        return;
    }


    int l = x_elems[0] < y_elems[0] ? x_elems[0] : y_elems[0];
    int u = x_elems[n-1] > y_elems[m-1] ? x_elems[n-1] : y_elems[m-1];

    auto xmax = encode_int_range_helper_variable(l-1, u, cnf_clauses);
    auto ymax = encode_int_range_helper_variable(l-1, u, cnf_clauses);

    set_max(*xmax, x, cnf_clauses);
    set_max(*ymax, y, cnf_clauses);

    int helper_x_id = next_helper_id++;
    int helper_y_id = next_helper_id++;

    for(int i = l; i <= u; i++){
        bool x_found = false;
        bool y_found = false;

        for(auto x_elem : x_elems){
            if(x_elem == i){
                x_found = true;
                break;
            } 
        }

        for(auto y_elem : y_elems){
            if(y_elem == i){
                y_found = true;
                break;
            } 
        }

        if(x_found){
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                                   make_literal(LiteralType::SET_ELEM, x.id, false, i)});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                                   make_literal(LiteralType::SET_ELEM, x.id, true, i)});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i)});
        }

        if(y_found){
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, true, i),
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, false, i),
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_y_id, false, i)});
        }
    }

    int helper_id = next_helper_id++; 

    for(int i = l; i <= u; i++){
        shared_ptr<Literal> yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper3 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper3 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                            make_literal(LiteralType::HELPER, helper_y_id, false, i),
                            not_helper1});
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                            make_literal(LiteralType::HELPER, helper_y_id, true, i),
                            not_helper1});                           
        if(i != u){
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                                not_helper2});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i+1),
                                not_helper2});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                                not_helper3});
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i+1),
                                not_helper3});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                                not_helper2});
            cnf_clauses.push_back({not_helper3});
        }
                               
        cnf_clauses.push_back({yes_helper1, yes_helper2, yes_helper3});

        shared_ptr<Literal> yes_helper4 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper4 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper5 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper5 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                               not_helper4});     
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, ymax->id, false, i),
                               not_helper4});                         
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                               not_helper5});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, ymax->id, true, i),
                               not_helper5});

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, false, i),
                               make_literal(LiteralType::HELPER, helper_y_id, true, i),
                               yes_helper4, yes_helper5});

        shared_ptr<Literal> yes_helper6 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper6 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        shared_ptr<Literal> yes_helper7 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        shared_ptr<Literal> not_helper7 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);


        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, i),
                               not_helper6});    
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, xmax->id, true, i-1),
                               not_helper6});                        
        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, i),
                               not_helper7});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, xmax->id, false, i-1),
                               not_helper7});

        cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_x_id, true, i),
                               make_literal(LiteralType::HELPER, helper_y_id, false, i),
                               yes_helper6, yes_helper7});

    }


    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, true, l),
                           make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

    cnf_clauses.push_back({make_literal(LiteralType::HELPER, helper_id, false, l),
                           make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
}

// Encodes a constraint of type x ⊆ y
void Encoder::encode_set_subset(const BasicVar& x, const BasicVar& y, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i])});
            i++;
        } else if(xs[i] > ys[j]){
           j++;
        } else {
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
        
            cnf_clauses.push_back({not_x, yes_y});    
            i++; j++;
        }
    }

    while(i < (int)xs.size())
        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i++])});

}

// Encodes a constraint of type (x ⊆ y) <=> r
void Encoder::encode_set_subset_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    encode_set_subset(x, y, temp_clauses);

    reify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type  r => (x ⊆ y)
void Encoder::encode_set_subset_imp(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    encode_set_subset(x, y, temp_clauses);

    impify(temp_clauses, r, cnf_clauses);

}


// Encodes a constraint of type x ⊇ y
void Encoder::encode_set_superset(const BasicVar& x, const BasicVar& y, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    encode_set_subset(y, x, cnf_clauses);
}

// Encodes a constraint of type (x ⊇ y) <=> r
void Encoder::encode_set_superset_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    encode_set_superset(x, y, temp_clauses);

    reify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type r => (x ⊇ y)
void Encoder::encode_set_superset_imp(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){

    vector<vector<shared_ptr<Literal>>> temp_clauses;
    encode_set_superset(x, y, temp_clauses);

    impify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type r = x Δ y (r = (x \ y) ∪ (y \ x))
void Encoder::encode_set_symdiff(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    auto rs = *get_set_elems(r);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            cnf_clauses.push_back({yes_x, not_r});
            cnf_clauses.push_back({not_x, yes_r});            
            i++;
        } else if(xs[i] > ys[j]){
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, ys[j]);
            shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
        
            cnf_clauses.push_back({yes_y, not_r});
            cnf_clauses.push_back({not_y, yes_r}); 
            j++;
        } else {
            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, xs[i]);
            shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, xs[i]);
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            cnf_clauses.push_back({not_r, yes_x, yes_y});
            cnf_clauses.push_back({not_r, not_x, not_y});
            cnf_clauses.push_back({yes_r, not_x, yes_y});
            cnf_clauses.push_back({yes_r, yes_x, not_y});
            i++; j++;
        }
    }

    while(i < (int)xs.size()){
        shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
        shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
        shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
        shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);

        cnf_clauses.push_back({yes_x, not_r});
        cnf_clauses.push_back({not_x, yes_r});            
        i++;
    }

    while(j < (int)ys.size()){
        shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
        shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, ys[j]);
        shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);
        shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
    
        cnf_clauses.push_back({yes_y, not_r});
        cnf_clauses.push_back({not_y, yes_r}); 
        j++;
    }
}

// Encodes a constraint of type r = x ∪ y
void Encoder::encode_set_union(const BasicVar& x, const BasicVar& y, const BasicVar& r, vector<vector<shared_ptr<Literal>>> &cnf_clauses){
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    auto rs = *get_set_elems(r);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            cnf_clauses.push_back({yes_x, not_r});
            cnf_clauses.push_back({not_x, yes_r});            
            i++;
        } else if(xs[i] > ys[j]){
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, ys[j]);
            shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
        
            cnf_clauses.push_back({yes_y, not_r});
            cnf_clauses.push_back({not_y, yes_r}); 
            j++;
        } else {
            shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, xs[i]);
            shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, xs[i]);
            shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            cnf_clauses.push_back({yes_r, not_x});
            cnf_clauses.push_back({yes_r, not_y});
            cnf_clauses.push_back({not_r, yes_x, yes_y});   
            i++; j++;
        }
    }

    while(i < (int)xs.size()){
        shared_ptr<Literal> yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
        shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
        shared_ptr<Literal> not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
        shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);

        cnf_clauses.push_back({yes_x, not_r});
        cnf_clauses.push_back({not_x, yes_r});            
        i++;
    }

    while(j < (int)ys.size()){
        shared_ptr<Literal> yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
        shared_ptr<Literal> yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, ys[j]);
        shared_ptr<Literal> not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);
        shared_ptr<Literal> not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
    
        cnf_clauses.push_back({yes_y, not_r});
        cnf_clauses.push_back({not_y, yes_r}); 
        j++;
    }
}