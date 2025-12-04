#include "nia_ls.h"
namespace nia
{
    // input transformation
    bool ls_solver::is_Number(const std::string& str)
    {
        for (char const &c : str) {
            if (std::isdigit(c) == 0) return false;
        }
        return true;
    }

    std::string ls_solver::delete_pa(std::string org)
    {
        int last = org.size();
        std::string now;
        for (int i = 0; i < org.size(); i++)
        {
            if (org[i] == ')')
            {
                last = i;
                break;
            }
        }
        now = org.substr(0, last);
        return now;
    }

    int ls_solver::is_pa(std::string org)
    {
        int flag=0;
        for(int i=0;i<org.size();i++)
        {
            if(org[i]==')'||org[i]=='(')
            {
                flag=1;
                break;
            }
        }
        return flag;
    }

    void ls_solver::split_string(std::string in_string, std::vector<std::string> &str_vec, std::string pattern = " ")
    {
        std::string::size_type pos;
        in_string += pattern;
        size_t size = in_string.size();
        for (size_t i = 0; i < size; i++)
        {
            pos = in_string.find(pattern, i);
            if (pos < size)
            {
                std::string s = in_string.substr(i, pos - i);
                str_vec.push_back(s);
                i = pos + pattern.size() - 1;
            }
        }
    }

    void ls_solver::build_lits(std::string &in_string)
    {
        // std::cout<<in_string<<std::endl;
        std::vector<std::string> vec;
        split_string(in_string, vec);
        if (vec[0] == "0")
        {
            _lits[0].lits_index = 0;
            return;
        } // true literal
        int lit_index = std::atoi(vec[0].c_str());
        lit *l = &(_lits[lit_index]);
        if (vec[1] == "or" || vec[1] == "if")
        {
            l->delta = transfer_name_to_resolution_var(vec[2], false);
            l->key = 1;
            l->is_nia_lit = false;
            l->lits_index = lit_index;
            return;
        } // or term in the form: 1 or newvar_2
        if (vec.size() > 2)
        {
            l->is_nia_lit = true;
            if (vec.size() > 6)
            {
                l->lits_index = std::atoi(vec[0].c_str());
                int idx = 5;
                if (vec[2] == "=" && vec[3] != "(")
                {
                    idx++;
                    l->key = -std::atoll(vec[3].c_str());
                }
                l->is_equal = (vec[2] == "=");
                bool single_mul = false;
                if (vec[idx - 1] == "*")
                {
                    idx -= 2;
                    single_mul = true;
                } // 849 ( = ( * lam6n64 rfc9 ) 0 ) now the idx at second '('
                for (; idx < vec.size(); idx++)
                {
                    if (vec[idx] == ")")
                    {
                        break;
                    }
                    if (vec[idx] == "(")
                    {
                        idx += 2;
                        term new_t;
                        if ((vec[idx][0] < '0' || vec[idx][0] > '9') && (vec[idx][0] != '-'))
                        { //( * global_invc1_0 lam1n4 )
                            while (vec[idx] != ")")
                            {
                                var_exp ve((int)transfer_name_to_tmp_var(vec[idx++]));
                                new_t.var_epxs.push_back(ve);
                            }
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                            if (single_mul)
                            {
                                break;
                            } // now the idx at ')'
                        }
                        else
                        {
                            __int128_t coff = std::atoll(vec[idx].c_str());
                            if (vec[++idx] == "(")
                            { //( * -1 ( * x y ) )idx at '('
                                idx += 2;
                                while (vec[idx] != ")")
                                {
                                    var_exp ve((int)transfer_name_to_tmp_var(vec[idx++]));
                                    new_t.var_epxs.push_back(ve);
                                }
                            }
                            else
                            { //( * 115 x ) idx at x
                                var_exp ve((int)transfer_name_to_tmp_var(vec[idx]));
                                new_t.var_epxs.push_back(ve);
                            }
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                            idx++;
                            if (single_mul)
                            {
                                break;
                            } // now the idx at ')'
                        }
                    }
                    else
                    {
                        term new_t;
                        new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(vec[idx])));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                    }
                    _num_opt += l->coff_terms.size();
                }
                if (vec[2] != "=" || vec[3] == "(")
                {
                    l->key = -std::atoll(vec[++idx].c_str());
                }
                if (vec[2] == ">=")
                {
                    l->key++;
                    invert_lit(*l);
                }
            } //( <= ( + x1 ( * -1 x2 ) x7 ( * -1 x8 ) ) 0 )
            else
            {
                l->lits_index = std::atoi(vec[0].c_str());
                if (vec[2] == "=" && vec.size() == 6 && (vec[3][0] < '0' || vec[3][0] > '9') && (vec[4][0] < '0' || vec[4][0] > '9') && (vec[3][0] != '-') && (vec[4][0] != '-'))
                {
                    l->is_equal = true;
                    l->key = 0;
                    term new_t_1, new_t_2;
                    var_exp ve_1((int)transfer_name_to_tmp_var(vec[3])), ve_2((int)transfer_name_to_tmp_var(vec[4]));
                    new_t_1.var_epxs.push_back(ve_1);
                    new_t_2.var_epxs.push_back(ve_2);
                    l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_1), 1));
                    l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_2), -1));
                } //( = x1 x2 )
                else
                {
                    __int128_t bound;
                    uint64_t var_idx;
                    if ((vec[3][0] < '0' || vec[3][0] > '9') && (vec[3][0] != '-'))
                    {
                        bound = std::atoll(vec[4].c_str());
                        var_idx = transfer_name_to_tmp_var(vec[3]);
                    } //( >= x 0 )
                    else
                    {
                        bound = std::atoll(vec[3].c_str());
                        var_idx = transfer_name_to_tmp_var(vec[4]);
                    } //( = 0 x )
                    term new_t;
                    new_t.var_epxs.push_back(var_exp((int)var_idx));
                    if (vec[2] == ">=")
                    {
                        l->key = bound;
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                    }
                    else
                    {
                        l->key = -bound;
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                    }
                    l->is_equal = (vec[2] == "=");
                } //( >= x 0 )
            }

        } // nia lit
        else
        {
            l->delta = transfer_name_to_resolution_var(vec[1], false);
            l->key = 1;
            l->is_nia_lit = false;
            l->lits_index = lit_index;
        } // boolean lit
    }

    void ls_solver::build_soft_lits(char * filename)
    {
        freopen(filename,"r",stdin);
        int soft_lits_nums;
        std::cin>>soft_lits_nums;
        //_num_lits=0;//revise
        int org_num=_num_lits;
        make_lits_space(_num_lits+soft_lits_nums);
        //org_num=0;//test ,delete after
        std::string in_string;
        getline(std::cin,in_string);
        for(int i=0;i<soft_lits_nums;i++)
        {
            getline(std::cin,in_string);
            // std::cout<<in_string<<std::endl;
            std::vector<std::string> vec;
            split_string(in_string, vec);
            int lit_index = std::atoi(vec[0].c_str())+org_num;
            // std::cout<<lit_index<<std::endl;
            lit *l = &(_lits[lit_index]);
            l->lits_index=lit_index;
            if(vec.size()>5)
            {
                l->is_nia_lit=true;
                l->is_soft=1;
                int idx;
                int is_not;
                int is_gt;
                bool single_mul=false;
                int is_key_neg=false;
                if (vec[1] == "(not")
                {
                    idx=4;
                    is_not=1;
                    l->is_not=1;
                    if (vec[2] == "(>=") is_gt = 1;
                    else is_gt = 0;
                    l->is_equal = (vec[2] == "(=");
                }
                else
                {
                    idx=3;
                    is_not=0;
                    if (vec[1] == "(>=") is_gt = 1;
                    else is_gt = 0;   
                    l->is_equal = (vec[1] == "(=");
                }                
                if (vec[idx - 1] == "(*")
                {
                    idx -= 1;
                    single_mul = true;
                } //849 (= (* lam6n64 rfc9) 0) now the idx at second '('
                for(;idx<vec.size();idx++)
                {
                    //(* 50001 lam102n0)
                    //(* (- 1) lam101n6)
                    //(* Nl2main_z1 lam101n12)
                    //(* (- 1) (* Nl2main_x1 lam10n12))
                    //8 (= 0 (+ lam4n0 (* (- 1) Nl2main_x2)))
                    //849 (= 0 (* lam6n64 rfc9))
                    if(idx==vec.size()-1)
                    {
                        //To be check :
                        //在vec小于5的里面，也有可能系数是负的，也有可能系数在前面
                        //小于5的里面check一下not的，然后总体check一遍 
                        //check single_mul
                        if(!is_key_neg)  l->key = -std::atoll(delete_pa(vec[idx]).c_str());//如果判定号是等号,那么系数有可能在前面 //849 (= 0 (* lam6n64 rfc9))
                        else l->key=std::atoll(delete_pa(vec[idx]).c_str());
                        if (is_gt==1)
                        {
                            l->key++;
                            invert_lit(*l);
                        }
                        break;
                    }
                    else if(vec[idx]=="(-")
                    {
                        is_key_neg=true;
                    }
                    else if (vec[idx] == "(*")
                    {
                        idx += 1;
                        term new_t;
                        if ((vec[idx][0] < '0' || vec[idx][0] > '9') && (vec[idx] != "(-"))
                        { //(* Nl2main_z1 lam101n12)
                            while (!is_pa(vec[idx]))
                            {
                                var_exp ve((int)transfer_name_to_tmp_var(vec[idx++]));
                                new_t.var_epxs.push_back(ve);
                            }
                            std::string cur_var=delete_pa(vec[idx]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                        else if((vec[idx]== "(-")&&(vec[idx+2][0] < '0' || vec[idx+2][0] > '9'))
                        {   //(* (- 1) lam101n6)
                            __int128_t coff = -std::atoll(delete_pa(vec[++idx]).c_str());
                            std::string cur_var=delete_pa(vec[++idx]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                        }
                        else if((vec[idx]== "(-")&&vec[idx+2]=="(*")
                        {   //(* (- 1) (* Nl2main_x1 lam10n12))
                            __int128_t coff = -std::atoll(delete_pa(vec[++idx]).c_str());
                            idx+=2;
                            while (!is_pa(vec[idx]))
                            {
                                var_exp ve((int)transfer_name_to_tmp_var(vec[idx++]));
                                new_t.var_epxs.push_back(ve);
                            }
                            std::string cur_var=delete_pa(vec[idx]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                        else
                        {   //(* 50001 lam102n0)
                            __int128_t coff = std::atoll(vec[idx++].c_str());
                            std::string cur_var=delete_pa(vec[idx]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                        }
                        if (single_mul)
                        {
                            break;//to be checked
                        } // now the idx at ')'
                    }
                    else
                    {
                        term new_t;
                        new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(vec[idx])));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                    }
                }
            }
            else 
            {
                l->is_nia_lit=true;
                l->is_soft=1;
                term new_t;
                if (vec[1] == "(not")
                {
                    l->is_not=1;//if 条件有问题
                    if (vec[2] == "(=" && vec.size() == 5 && (vec[3][0] < '0' || vec[3][0] > '9') && (vec[4][0] < '0' || vec[4][0] > '9') && (vec[3] != "(-") && (vec[4] != "(-"))
                    {
                        // std::cout<<"here1"<<std::endl;
                        l->is_equal = true;
                        l->key = 0;
                        term new_t_1, new_t_2;
                        std::string var_name=delete_pa(vec[4]);
                        var_exp ve_1((int)transfer_name_to_tmp_var(vec[3])), ve_2((int)transfer_name_to_tmp_var(var_name));
                        new_t_1.var_epxs.push_back(ve_1);
                        new_t_2.var_epxs.push_back(ve_2);
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_1), 1));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_2), -1));
                    } //20 (not (= x1 x2))
                    else
                    {
                        __int128_t bound;
                        uint64_t var_idx;
                        if ((vec[3][0] < '0' || vec[3][0] > '9') && (vec[3]!= "(-"))
                        {
                            // std::cout<<"here2"<<std::endl;
                            if(vec[4]=="(-")  bound = -std::atoll(delete_pa(vec[5]).c_str());
                            else  bound = std::atoll(delete_pa(vec[4]).c_str());
                            var_idx = transfer_name_to_tmp_var(vec[3]);
                        } //20 (not (>= lam5n0 0)) //20 (not (>= xH457 (- 250)))
                        else if((vec[4][0] < '0' || vec[4][0] > '9') && (vec[4] != "(-"))
                        {
                            // std::cout<<"here3"<<std::endl;
                            int idx=4;
                            if(vec[3]=="(-")  {bound = -std::atoll(delete_pa(vec[4]).c_str());idx++;}
                            else  bound = std::atoll(delete_pa(vec[3]).c_str());
                            std::string var_name=delete_pa(vec[idx]);
                            var_idx = transfer_name_to_tmp_var(var_name);
                        } //6 (not (= 0 x)) //6 (not (= (- 100) x))
                        term new_t;
                        new_t.var_epxs.push_back(var_exp((int)var_idx));
                        if (vec[2] == "(>=")
                        {
                            l->key = bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                        }
                        else
                        {
                            l->key = -bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                        l->is_equal = (vec[2] == "(=");
                    }
                }
                else 
                {
                    
                    if (vec[1] == "(=" && vec.size() == 4 && (vec[2][0] < '0' || vec[2][0] > '9') && (vec[3][0] < '0' || vec[3][0] > '9') && (vec[2] != "(-") && (vec[3] != "(-"))
                    {
                        l->is_equal = true;
                        l->key = 0;
                        term new_t_1, new_t_2;
                        std::string var_name=delete_pa(vec[3]);
                        var_exp ve_1((int)transfer_name_to_tmp_var(vec[2])), ve_2((int)transfer_name_to_tmp_var(var_name));
                        new_t_1.var_epxs.push_back(ve_1);
                        new_t_2.var_epxs.push_back(ve_2);
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_1), 1));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_2), -1));
                    } //20 (= x1 x2)
                    else
                    {
                        __int128_t bound;
                        uint64_t var_idx;
                        if ((vec[2][0] < '0' || vec[2][0] > '9') && (vec[2]!= "(-"))
                        {
                            if(vec[3]=="(-")  bound = -std::atoll(delete_pa(vec[4]).c_str());
                            else  bound = std::atoll(delete_pa(vec[3]).c_str());
                            var_idx = transfer_name_to_tmp_var(vec[2]);
                        } //20 (not (>= lam5n0 0)) //20 (not (>= xH457 (- 250)))
                        else if((vec[3][0] < '0' || vec[3][0] > '9') && (vec[3] != "(-"))
                        {
                            int idx=3;
                            if(vec[2]=="(-")  {bound = -std::atoll(delete_pa(vec[3]).c_str());idx++;}
                            else  bound = std::atoll(delete_pa(vec[2]).c_str());
                            std::string var_name=delete_pa(vec[idx]);
                            var_idx = transfer_name_to_tmp_var(var_name);
                        } //6 (= 0 x)) //6 (not (= (- 100) x))
                        term new_t;
                        new_t.var_epxs.push_back(var_exp((int)var_idx));
                        if (vec[1] == "(>=")
                        {
                            l->key = bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                        }
                        else
                        {
                            l->key = -bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                        l->is_equal = (vec[1] == "=");
                    }
                }
            }
        }
        //clause
        int soft_clause_num;
        std::cin>>soft_clause_num;
        getline(std::cin,in_string);
        _soft_clauses.resize(soft_clause_num);
        for(int i=0;i<soft_clause_num;i++)
        {
            getline(std::cin,in_string);
            std::vector<std::string> vec;
            split_string(in_string, vec);
            std::vector<int> cur_clause;
            for(int j=0;j<vec.size();j++)
            {
                // std::cout<<vec[j]<<std::endl;
                if(vec[j]=="") continue;
                // std::cout<<vec[j]<<std::endl;
                int real_index=org_num+stoi(vec[j]);
                int not_flag=_lits[real_index].is_not;
                if(not_flag==0) 
                {
                    _soft_clauses[i].literals.push_back(real_index);//处理not
                    std::cout<<real_index<<" ";
                }
                else 
                {
                    _soft_clauses[i].literals.push_back(-real_index);
                    std::cout<<-real_index<<" ";
                }
                cur_clause.push_back(stoi(vec[j]));
            }
            std::cout<<std::endl;
            soft_clauses.push_back(cur_clause);
        }
        for(int i=0;i<soft_clause_num;i++)
        {
            getline(std::cin,in_string);
            // std::cout<<in_string<<std::endl;
            soft_clauses_weight.push_back(stoi(in_string));
        }
        _num_soft_clauses=_soft_clauses.size();
        //clause
        fclose(stdin);
        h_inc=1;
        for(int i=0;i<soft_clauses_weight.size();i++)
        {
            if(soft_clauses_weight[i]!=1) 
            {
                h_inc=3;
                //break;
            }
            _soft_clauses[i].org_weight=soft_clauses_weight[i];//初始权重
        }
        // for(int i=0;i<soft_clauses_weight.size();i++)
        // {
        //     std::cout<<_soft_clauses[i].org_weight<<std::endl;
        // }
        // exit(0);
        // std::cout<<_num_lits<<std::endl;
        // for(int i=0;i<_num_lits;i++)
        // {
        //     print_literal(_lits[i]);
        // }
        exit(0);
    }

    bool ls_solver::build_new_hard_lits(char * filename,std::vector<std::vector<int>> &new_hard_clauses,bool is_with_hard)
    {
        bool is_or_hard=false;
        freopen(filename,"r",stdin);
        std::string file_type;
        std::string in_string;
        std::cin>>file_type; 
        getline(std::cin,in_string);
        if(file_type=="edge"||file_type=="safe50or"||file_type=="safe50")
        {
            is_or_hard=true;
        }
        else if(file_type=="term")
        {
            is_or_hard=false;
        }
        std::string cache;
        int soft_lits_nums;
        std::cin>>cache;
        if(cache=="not pBounded"||cache=="not")
        {
            std::cout<<"not pBounded not considered";
            exit(0);
        }
        soft_lits_nums=stoi(cache);
        if(soft_lits_nums==0)
        {
            std::cout<<"Not MaxSMT Problem";
            exit(0);
        }
        //_num_lits=0;//revise
        int org_num=_num_lits;
        make_lits_space(_num_lits+soft_lits_nums);
        //org_num=0;//test ,delete after
        getline(std::cin,in_string);
        //解析软文字
        for(int i=0;i<soft_lits_nums;i++)
        {
            getline(std::cin,in_string);
            // std::cout<<in_string<<std::endl;
            std::vector<std::string> vec;
            split_string(in_string, vec);
            int lit_index = std::atoi(vec[0].c_str())+org_num;
            // std::cout<<lit_index<<std::endl;
            lit *l = &(_lits[lit_index]);
            l->lits_index=lit_index;
            if( count(in_string.begin(),in_string.end(),'+')==1 && vec[2]!="(+" &&vec[1]=="(=")
            {
                l->is_equal=true;
                l->is_nia_lit=true;//new add
                if (vec[1] == "(not") l->is_not=1;
                else l->is_not=0;
                l->key=0;
                //first var init
                term new_t;
                new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(vec[2])));
                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                //second vars init
                int first_add_index=in_string.find("(+");
                std::string second_string=in_string.substr(first_add_index,in_string.size()-first_add_index);//to be check
                std::vector<std::string> vec_2;
                split_string(second_string, vec_2);
                int idx_2=1;
                for(;idx_2<vec_2.size();idx_2++)
                {
                    if (vec_2[idx_2] == "(*")
                    {
                        idx_2 += 1;
                        term new_t;
                        if((vec_2[idx_2]== "(-")&&(vec_2[idx_2+2][0] < '0' || vec_2[idx_2+2][0] > '9'))
                        {   //(* (- 1) lam101n6)
                            __int128_t coff = -std::atoll(delete_pa(vec_2[++idx_2]).c_str());
                            std::string cur_var=delete_pa(vec_2[++idx_2]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -coff));
                        }
                        else
                        {
                            std::cout<<"complier error1: equal lits has pos coff "<< std::endl;
                            idx_2++;
                            term mew_t;
                            __int128_t coff = std::atoll(vec_2[idx_2].c_str());
                            std::string cur_var=delete_pa(vec_2[++idx_2]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -coff));
                        }
                    }
                    else
                    {
                        term new_t;
                        std::string cur_var=delete_pa(vec_2[idx_2]);
                        new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(cur_var)));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                    }
                }
                continue;
            }
            if(count(in_string.begin(),in_string.end(),'+')==2)//这里有问题,并且没放到软子句那里
            {
                bool has_delt=false;
                int pos =vec.size()-1;
                std::string cur=delete_pa(vec[pos]);
                if(is_Number(cur)) has_delt=true;
                if(!has_delt)
                {
                    l->is_equal=true;
                    l->is_soft=1;//new add
                    l->is_nia_lit=true;//new add
                    if (vec[1] == "(not") l->is_not=1;
                    else l->is_not=0;
                    l->key=0;
                    int first_add_index=in_string.find("(+");
                    int second_add_index=in_string.find("(+",first_add_index+2);
                    std::string first_string=in_string.substr(first_add_index,second_add_index-first_add_index-1);//to be check
                    std::string second_string=in_string.substr(second_add_index,in_string.size()-second_add_index);//to be check
                    std::vector<std::string> vec_1,vec_2;
                    split_string(first_string, vec_1);
                    split_string(second_string, vec_2);
                    int idx_1=1;
                    int idx_2=1;
                    for(;idx_1<vec_1.size();idx_1++)
                    {
                        if (vec_1[idx_1] == "(*")
                        {
                            idx_1 += 1;
                            term new_t;
                            if((vec_1[idx_1]== "(-")&&(vec_1[idx_1+2][0] < '0' || vec_1[idx_1+2][0] > '9'))
                            {   //(* (- 1) lam101n6)
                                __int128_t coff = -std::atoll(delete_pa(vec_1[++idx_1]).c_str());
                                std::string cur_var=delete_pa(vec_1[++idx_1]);
                                var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                new_t.var_epxs.push_back(ve);
                                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                            }
                            else
                            {
                                std::cout<<"complier error1: equal lits has pos coff "<< std::endl;
                                idx_1++;
                                term mew_t;
                                __int128_t coff = std::atoll(vec_1[idx_1].c_str());
                                std::string cur_var=delete_pa(vec_1[++idx_1]);
                                var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                new_t.var_epxs.push_back(ve);
                                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                            }
                        }
                        else
                        {
                            term new_t;
                            std::string cur_var=delete_pa(vec_1[idx_2]);
                            new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(cur_var)));
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                    }
                    for(;idx_2<vec_2.size();idx_2++)
                    {
                        if (vec_2[idx_2] == "(*")
                        {
                            idx_2 += 1;
                            term new_t;
                            if((vec_2[idx_2]== "(-")&&(vec_2[idx_2+2][0] < '0' || vec_2[idx_2+2][0] > '9'))
                            {   //(* (- 1) lam101n6)
                                __int128_t coff = -std::atoll(delete_pa(vec_2[++idx_2]).c_str());
                                std::string cur_var=delete_pa(vec_2[++idx_2]);
                                var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                new_t.var_epxs.push_back(ve);
                                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -coff));
                            }
                            else
                            {
                                std::cout<<"complier error1: equal lits has pos coff "<< std::endl;
                                idx_2++;
                                term mew_t;
                                __int128_t coff = std::atoll(vec_2[idx_2].c_str());
                                std::string cur_var=delete_pa(vec_2[++idx_2]);
                                var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                new_t.var_epxs.push_back(ve);
                                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -coff));
                            }
                        }
                        else
                        {
                            term new_t;
                                std::string cur_var=delete_pa(vec_2[idx_2]);
                            new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(cur_var)));
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                        }
                    }
                    continue;
                }
            }
            if(vec.size()>5)
            {
                l->is_nia_lit=true;
                l->is_soft=1;
                int idx;
                int is_not;
                int is_gt;
                bool single_mul=false;
                int is_key_neg=false;
                if (vec[1] == "(not")
                {
                    idx=4;
                    is_not=1;
                    l->is_not=1;
                    if (vec[2] == "(>=") is_gt = 1;
                    else is_gt = 0;
                    l->is_equal = (vec[2] == "(=");
                }
                else
                {
                    idx=3;
                    is_not=0;
                    if (vec[1] == "(>=") is_gt = 1;
                    else is_gt = 0;   
                    l->is_equal = (vec[1] == "(=");
                }                
                if (vec[idx - 1] == "(*")
                {
                    idx -= 1;
                    single_mul = true;
                } //849 (= (* lam6n64 rfc9) 0) now the idx at second '('
                for(;idx<vec.size();idx++)
                {
                    //(* 50001 lam102n0)
                    //(* (- 1) lam101n6)
                    //(* Nl2main_z1 lam101n12)
                    //(* (- 1) (* Nl2main_x1 lam10n12))
                    //8 (= 0 (+ lam4n0 (* (- 1) Nl2main_x2)))
                    //849 (= 0 (* lam6n64 rfc9))
                    if(idx==vec.size()-1)
                    {
                        //To be check :
                        //在vec小于5的里面，也有可能系数是负的，也有可能系数在前面
                        //小于5的里面check一下not的，然后总体check一遍 
                        //check single_mul
                        if(!is_key_neg)  l->key = -std::atoll(delete_pa(vec[idx]).c_str());//如果判定号是等号,那么系数有可能在前面 //849 (= 0 (* lam6n64 rfc9))
                        else l->key=std::atoll(delete_pa(vec[idx]).c_str());
                        if (is_gt==1)
                        {
                            l->key++;
                            invert_lit(*l);
                        }
                        break;
                    }
                    else if(vec[idx]=="(-")
                    {
                        is_key_neg=true;
                    }
                    else if (vec[idx] == "(*")
                    {
                        idx += 1;
                        term new_t;
                        if ((vec[idx][0] < '0' || vec[idx][0] > '9') && (vec[idx] != "(-"))
                        { //(* Nl2main_z1 lam101n12)
                            if(idx+1<=vec.size()-1&&vec[idx+1]=="(+")
                            {
                                var_exp first((int)transfer_name_to_tmp_var(vec[idx]));
                                idx+=2;
                                while(true)
                                {
                                    term new_t_special;
                                    new_t_special.var_epxs.push_back(first);
                                    if(vec[idx]=="(*" && vec[idx+1] =="(-")
                                    {
                                        idx++;
                                        __int128_t coff = -std::atoll(delete_pa(vec[++idx]).c_str());
                                        std::string cur_var=delete_pa(vec[++idx]);
                                        var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                        new_t_special.var_epxs.push_back(ve);
                                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_special), coff));
                                    }
                                    else if(vec[idx]=="(*" && is_Number(vec[idx+1]) )
                                    {
                                        __int128_t coff = std::atoll(delete_pa(vec[++idx]).c_str());
                                        std::string cur_var=delete_pa(vec[++idx]);
                                        var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                        new_t_special.var_epxs.push_back(ve);
                                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_special), coff));
                                    }
                                    else if(!is_Number(vec[idx]))
                                    {
                                        std::string cur_var=delete_pa(vec[idx]);
                                        var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                        new_t_special.var_epxs.push_back(ve);
                                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_special), 1));
                                    }
                                    if(count(vec[idx].begin(),vec[idx].end(),')')>=2) break;
                                    else idx++;
                                }
                            }
                            else
                            {
                                while (!is_pa(vec[idx]))
                                {
                                    var_exp ve((int)transfer_name_to_tmp_var(vec[idx++]));
                                    new_t.var_epxs.push_back(ve);
                                }
                                std::string cur_var=delete_pa(vec[idx]);
                                var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                new_t.var_epxs.push_back(ve);
                                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                            }
                        }
                        else if((vec[idx]== "(-")&&(vec[idx+2][0] < '0' || vec[idx+2][0] > '9'))
                        {   //(* (- 1) lam101n6)
                            __int128_t coff = -std::atoll(delete_pa(vec[++idx]).c_str());
                            std::string cur_var=delete_pa(vec[++idx]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                        }
                        else if((vec[idx]== "(-")&&vec[idx+2]=="(*")
                        {   //(* (- 1) (* Nl2main_x1 lam10n12))
                            __int128_t coff = -std::atoll(delete_pa(vec[++idx]).c_str());
                            idx+=2;
                            while (!is_pa(vec[idx]))
                            {
                                var_exp ve((int)transfer_name_to_tmp_var(vec[idx++]));
                                new_t.var_epxs.push_back(ve);
                            }
                            std::string cur_var=delete_pa(vec[idx]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                        else
                        {   //(* 50001 lam102n0)
                            __int128_t coff = std::atoll(vec[idx++].c_str());
                            std::string cur_var=delete_pa(vec[idx]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                        }
                        if (single_mul)
                        {
                            break;//to be checked
                        } // now the idx at ')'
                    }
                    else
                    {
                        term new_t;
                        std::string cur_var=delete_pa(vec[idx]);
                        new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(cur_var)));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                    }
                }
            }
            else 
            {
                l->is_nia_lit=true;
                l->is_soft=1;
                term new_t;
                if (vec[1] == "(not")
                {
                    l->is_not=1;//if 条件有问题
                    if (vec[2] == "(=" && vec.size() == 5 && (vec[3][0] < '0' || vec[3][0] > '9') && (vec[4][0] < '0' || vec[4][0] > '9') && (vec[3] != "(-") && (vec[4] != "(-"))
                    {
                        // std::cout<<"here1"<<std::endl;
                        l->is_equal = true;
                        l->key = 0;
                        term new_t_1, new_t_2;
                        std::string var_name=delete_pa(vec[4]);
                        var_exp ve_1((int)transfer_name_to_tmp_var(vec[3])), ve_2((int)transfer_name_to_tmp_var(var_name));
                        new_t_1.var_epxs.push_back(ve_1);
                        new_t_2.var_epxs.push_back(ve_2);
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_1), 1));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_2), -1));
                    } //20 (not (= x1 x2))
                    else
                    {
                        __int128_t bound;
                        uint64_t var_idx;
                        if ((vec[3][0] < '0' || vec[3][0] > '9') && (vec[3]!= "(-"))
                        {
                            // std::cout<<"here2"<<std::endl;
                            if(vec[4]=="(-")  bound = -std::atoll(delete_pa(vec[5]).c_str());
                            else  bound = std::atoll(delete_pa(vec[4]).c_str());
                            var_idx = transfer_name_to_tmp_var(vec[3]);
                        } //20 (not (>= lam5n0 0)) //20 (not (>= xH457 (- 250)))
                        else if((vec[4][0] < '0' || vec[4][0] > '9') && (vec[4] != "(-"))
                        {
                            // std::cout<<"here3"<<std::endl;
                            int idx=4;
                            if(vec[3]=="(-")  {bound = -std::atoll(delete_pa(vec[4]).c_str());idx++;}
                            else  bound = std::atoll(delete_pa(vec[3]).c_str());
                            std::string var_name=delete_pa(vec[idx]);
                            var_idx = transfer_name_to_tmp_var(var_name);
                        } //6 (not (= 0 x)) //6 (not (= (- 100) x))
                        term new_t;
                        new_t.var_epxs.push_back(var_exp((int)var_idx));
                        if (vec[2] == "(>=")
                        {
                            l->key = bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                        }
                        else
                        {
                            l->key = -bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                        l->is_equal = (vec[2] == "(=");
                    }
                }
                else 
                {
                    
                    if (vec[1] == "(=" && vec.size() == 4 && (vec[2][0] < '0' || vec[2][0] > '9') && (vec[3][0] < '0' || vec[3][0] > '9') && (vec[2] != "(-") && (vec[3] != "(-"))
                    {
                        l->is_equal = true;
                        l->key = 0;
                        term new_t_1, new_t_2;
                        std::string var_name=delete_pa(vec[3]);
                        var_exp ve_1((int)transfer_name_to_tmp_var(vec[2])), ve_2((int)transfer_name_to_tmp_var(var_name));
                        new_t_1.var_epxs.push_back(ve_1);
                        new_t_2.var_epxs.push_back(ve_2);
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_1), 1));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_2), -1));
                    } //20 (= x1 x2)
                    else
                    {
                        __int128_t bound;
                        uint64_t var_idx;
                        if ((vec[2][0] < '0' || vec[2][0] > '9') && (vec[2]!= "(-"))
                        {
                            if(vec[3]=="(-")  bound = -std::atoll(delete_pa(vec[4]).c_str());
                            else  bound = std::atoll(delete_pa(vec[3]).c_str());
                            var_idx = transfer_name_to_tmp_var(vec[2]);
                        } //20 (not (>= lam5n0 0)) //20 (not (>= xH457 (- 250)))
                        else if((vec[3][0] < '0' || vec[3][0] > '9') && (vec[3] != "(-"))
                        {
                            int idx=3;
                            if(vec[2]=="(-")  {bound = -std::atoll(delete_pa(vec[3]).c_str());idx++;}
                            else  bound = std::atoll(delete_pa(vec[2]).c_str());
                            std::string var_name=delete_pa(vec[idx]);
                            var_idx = transfer_name_to_tmp_var(var_name);
                        } //6 (= 0 x)) //6 (not (= (- 100) x))
                        term new_t;
                        new_t.var_epxs.push_back(var_exp((int)var_idx));
                        if (vec[1] == "(>=")
                        {
                            l->key = bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                        }
                        else
                        {
                            l->key = -bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                        l->is_equal = (vec[1] == "(=");
                    }
                }
            }
        }
        //clause
        int soft_clause_num;
        std::cin>>soft_clause_num;
        getline(std::cin,in_string);
        _soft_clauses.resize(soft_clause_num);
        //解析软子句
        for(int i=0;i<soft_clause_num;i++)
        {
            getline(std::cin,in_string);
            std::vector<std::string> vec;
            split_string(in_string, vec);
            std::vector<int> cur_clause;
            for(int j=0;j<vec.size();j++)
            {
                // std::cout<<vec[j]<<std::endl;
                if(vec[j]=="") continue;
                // std::cout<<vec[j]<<std::endl;
                int real_index=org_num+stoi(vec[j]);
                int not_flag=_lits[real_index].is_not;
                if(not_flag==0) 
                {
                    _soft_clauses[i].literals.push_back(real_index);//处理not
                }
                else 
                {
                    _soft_clauses[i].literals.push_back(-real_index);
                }
                cur_clause.push_back(stoi(vec[j]));
            }
            soft_clauses.push_back(cur_clause);
        }
        for(int i=0;i<soft_clause_num;i++)
        {
            getline(std::cin,in_string);
            // std::cout<<in_string<<std::endl;
            soft_clauses_weight.push_back(stoi(in_string));
        }
        _num_soft_clauses=_soft_clauses.size();
        //clause
        h_inc=1;
        //解析软子句权重
        for(int i=0;i<soft_clauses_weight.size();i++)
        {
            if(soft_clauses_weight[i]!=1) 
            {
                h_inc=3;
                //break;
            }
            _soft_clauses[i].org_weight=soft_clauses_weight[i];//初始权重
        }
        if(!is_or_hard||!is_with_hard) 
        {
            fclose(stdin);
            // for(int i=0;i<_num_lits;i++)
            // {
            //     std::cout<<i<<"  ";
            //     print_literal(_lits[i]);
            // }
            // exit(0);
            return is_or_hard;
        }
        //new add hard clause part
        org_num=_num_lits;
        int new_hard_lits_num;
        getline(std::cin,in_string);
        new_hard_lits_num=stoi(in_string);
        make_lits_space(_num_lits+new_hard_lits_num);
        // std::cout<<"here"<<std::endl;
        //9 (= (+ __rho_1_^0 (* (- 1) var_e_EFAFp_0___rho_1_^0)) (+ __const_5^0 (* (- 1) undef52312)))
        //15 (<= (+ Nl186CT1 (* (- 1) Nl186var_Le_AFp_4_x^01) (* (- 1) Nl186var_e_EFAFp_0_x^01) (* Nl186__disjvr_10^01 __disjvr_10^0) (* Nl186__disjvr_11^01 __disjvr_11^0) (* Nl186__disjvr_12^01 __disjvr_12^0) (* Nl186__disjvr_6^01 __disjvr_6^0) (* Nl186__disjvr_7^01 __disjvr_7^0) (* Nl186__disjvr_8^01 __disjvr_8^0) (* Nl186__disjvr_9^01 __disjvr_9^0) (* Nl186copied12^01 copied12^0) (* Nl186copied13^01 copied13^0) (* Nl186copied8^01 copied8^0) (* Nl186copied9^01 copied9^0) (* Nl186ndi10^01 ndi10^0) (* Nl186rv_LLe_p^01 rv_LLe_p^0) (* Nl186rv_Le_AFp^01 rv_Le_AFp^0) (* Nl186var_LLe_p_0_p^01 var_LLe_p_0_p^0) (* Nl186var_LLe_p_4_p^01 var_LLe_p_4_p^0) (* Nl186var_Le_AFp_2___rho_1_^01 var_Le_AFp_2___rho_1_^0) (* Nl186var_Le_AFp_2___rho_2_^01 var_Le_AFp_2___rho_2_^0) (* Nl186var_Le_AFp_2_p^01 var_Le_AFp_2_p^0) (* Nl186var_Le_AFp_2_rv_init^01 var_Le_AFp_2_rv_init^0) (* Nl186var_Le_AFp_2_x^01 var_Le_AFp_2_x^0) (* Nl186var_Le_AFp_2_y^01 var_Le_AFp_2_y^0) (* Nl186var_Le_AFp_6___rho_1_^01 var_Le_AFp_6___rho_1_^0) (* Nl186var_Le_AFp_6___rho_2_^01 var_Le_AFp_6___rho_2_^0) (* Nl186var_Le_AFp_6_p^01 var_Le_AFp_6_p^0) (* Nl186var_Le_AFp_6_rv_init^01 var_Le_AFp_6_rv_init^0) (* Nl186var_Le_AFp_6_x^01 var_Le_AFp_6_x^0) (* Nl186var_Le_AFp_6_y^01 var_Le_AFp_6_y^0) (* var_e_EFAFp_0___rho_2_^0 (+ Nl186var_Le_AFp_4___rho_2_^01 Nl186var_e_EFAFp_0___rho_2_^01)) (* var_e_EFAFp_0_p^0 (+ Nl186var_Le_AFp_4_p^01 Nl186var_e_EFAFp_0_p^01)) (* var_e_EFAFp_0_rv_init^0 (+ Nl186var_Le_AFp_4_rv_init^01 Nl186var_e_EFAFp_0_rv_init^01)) (* var_e_EFAFp_0_x^0 (+ Nl186var_Le_AFp_4_x^01 Nl186var_e_EFAFp_0_x^01)) (* var_e_EFAFp_0_y^0 (+ Nl186var_Le_AFp_4_y^01 Nl186var_e_EFAFp_0_y^01)) (* undef62256 (+ Nl186var_Le_AFp_4___rho_1_^01 Nl186var_e_EFAFp_0___rho_1_^01))) 0)
        //11 (= (+ undef198 (* (- 1) undef309)) (+ (* (- 1) a_178^0) undef280))
        //解析硬文字
        //(* undef94 (+ (* (- 1) Nl5arg21) (* (- 1) Nl5arg41) (* (- 1) Nl5arg61)))) 0)
        //(<= (+ Nl5CT1 (* undef93 (+ (* (- 1) Nl5arg11) (* (- 1) Nl5arg31) (* (- 1) Nl5arg51))) (* undef94 (+ (* (- 1) Nl5arg21) (* (- 1) Nl5arg41) (* (- 1) Nl5arg61)))) 0)
        for(int i=0;i<new_hard_lits_num;i++)
        {
            getline(std::cin,in_string);
            std::vector<std::string> vec;
            split_string(in_string, vec);
            int lit_index = std::atoi(vec[0].c_str())+org_num-1;//this -1
            // std::cout<<lit_index<<std::endl;
            lit *l = &(_lits[lit_index]);
            l->lits_index=lit_index;
            // std::cout<<l->lits_index<<std::endl;
            if( count(in_string.begin(),in_string.end(),'+')==1 && vec[2]!="(+" &&vec[1]=="(=")
            {
                l->is_equal=true;
                l->is_nia_lit=true;//new add
                if (vec[1] == "(not") l->is_not=1;
                else l->is_not=0;
                l->key=0;
                //first var init
                term new_t;
                new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(vec[2])));
                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                //second vars init
                int first_add_index=in_string.find("(+");
                std::string second_string=in_string.substr(first_add_index,in_string.size()-first_add_index);//to be check
                std::vector<std::string> vec_2;
                split_string(second_string, vec_2);
                int idx_2=1;
                for(;idx_2<vec_2.size();idx_2++)
                {
                    if (vec_2[idx_2] == "(*")
                    {
                        idx_2 += 1;
                        term new_t;
                        if((vec_2[idx_2]== "(-")&&(vec_2[idx_2+2][0] < '0' || vec_2[idx_2+2][0] > '9'))
                        {   //(* (- 1) lam101n6)
                            __int128_t coff = -std::atoll(delete_pa(vec_2[++idx_2]).c_str());
                            std::string cur_var=delete_pa(vec_2[++idx_2]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -coff));
                        }
                        else
                        {
                            std::cout<<"complier error1: equal lits has pos coff "<< std::endl;
                            idx_2++;
                            term mew_t;
                            __int128_t coff = std::atoll(vec_2[idx_2].c_str());
                            std::string cur_var=delete_pa(vec_2[++idx_2]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -coff));
                        }
                    }
                    else
                    {
                        term new_t;
                        std::string cur_var=delete_pa(vec_2[idx_2]);
                        new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(cur_var)));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                    }
                }
                continue;
            }
            if(count(in_string.begin(),in_string.end(),'+')==2)//这里有问题,并且没放到软子句那里
            {//进了这里就有两种情况，等号然后两个+lit相等，还有一种是出现+ 号和 (* undef94 (+ (* (- 1) Nl5arg21) (* (- 1) Nl5arg41) (* (- 1) Nl5arg61)))) 这种情况delt不会出现在前面
            //delt出现在前面只有一种情况，849 (= 0 (* lam6n64 rfc9))，也就是没有+号，所以只需要判断最后一个delt就能判断出是不是这种情况就可以了
                bool has_delt=false;
                int pos =vec.size()-1;
                std::string cur=delete_pa(vec[pos]);
                if(is_Number(cur)) has_delt=true;
                if(!has_delt)
                {
                    //11 (= (+ undef198 (* (- 1) undef309)) (+ (* (- 1) a_178^0) undef280))
                    l->is_equal=true;
                    l->is_nia_lit=true;//new add
                    if (vec[1] == "(not") l->is_not=1;
                    else l->is_not=0;
                    l->key=0;
                    int first_add_index=in_string.find("(+");
                    int second_add_index=in_string.find("(+",first_add_index+2);
                    std::string first_string=in_string.substr(first_add_index,second_add_index-first_add_index-1);//to be check
                    std::string second_string=in_string.substr(second_add_index,in_string.size()-second_add_index);//to be check
                    std::vector<std::string> vec_1,vec_2;
                    split_string(first_string, vec_1);
                    split_string(second_string, vec_2);
                    int idx_1=1;
                    int idx_2=1;
                    //4 (= (+ var_e_EFAFp_0_y^0 (* (- 1) y^0)) (+ __const_5^0 (* (- 1) undef52312)))
                    for(;idx_1<vec_1.size();idx_1++)
                    {
                        if (vec_1[idx_1] == "(*")
                        {
                            idx_1 += 1;
                            term new_t;
                            if((vec_1[idx_1]== "(-")&&(vec_1[idx_1+2][0] < '0' || vec_1[idx_1+2][0] > '9'))
                            {   //(* (- 1) lam101n6)
                                __int128_t coff = -std::atoll(delete_pa(vec_1[++idx_1]).c_str());
                                std::string cur_var=delete_pa(vec_1[++idx_1]);
                                var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                new_t.var_epxs.push_back(ve);
                                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                            }
                            else
                            {
                                std::cout<<"complier error1: equal lits has pos coff "<< std::endl;
                                idx_1++;
                                term mew_t;
                                __int128_t coff = std::atoll(vec_1[idx_1].c_str());
                                std::string cur_var=delete_pa(vec_1[++idx_1]);
                                var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                new_t.var_epxs.push_back(ve);
                                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                            }
                        }
                        else
                        {
                            term new_t;
                            std::string cur_var=delete_pa(vec_1[idx_2]);
                            new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(cur_var)));
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                    }
                    for(;idx_2<vec_2.size();idx_2++)
                    {
                        if (vec_2[idx_2] == "(*")
                        {
                            idx_2 += 1;
                            term new_t;
                            if((vec_2[idx_2]== "(-")&&(vec_2[idx_2+2][0] < '0' || vec_2[idx_2+2][0] > '9'))
                            {   //(* (- 1) lam101n6)
                                __int128_t coff = -std::atoll(delete_pa(vec_2[++idx_2]).c_str());
                                std::string cur_var=delete_pa(vec_2[++idx_2]);
                                var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                new_t.var_epxs.push_back(ve);
                                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -coff));
                            }
                            else
                            {
                                std::cout<<"complier error1: equal lits has pos coff "<< std::endl;
                                idx_2++;
                                term mew_t;
                                __int128_t coff = std::atoll(vec_2[idx_2].c_str());
                                std::string cur_var=delete_pa(vec_2[++idx_2]);
                                var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                new_t.var_epxs.push_back(ve);
                                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -coff));
                            }
                        }
                        else
                        {
                            term new_t;
                            std::string cur_var=delete_pa(vec_2[idx_2]);
                            new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(cur_var)));
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                        }
                    }
                    continue;
                }
            }
            if(vec.size()>5)
            {
                l->is_nia_lit=true;
                l->is_soft=1;
                int idx;
                int is_not;
                int is_gt;
                bool single_mul=false;
                int is_key_neg=false;
                if (vec[1] == "(not")
                {
                    idx=4;
                    is_not=1;
                    l->is_not=1;
                    if (vec[2] == "(>=") is_gt = 1;
                    else is_gt = 0;
                    l->is_equal = (vec[2] == "(=");
                }
                else
                {
                    idx=3;
                    is_not=0;
                    if (vec[1] == "(>=") is_gt = 1;
                    else is_gt = 0;   
                    l->is_equal = (vec[1] == "(=");
                }                
                if (vec[idx - 1] == "(*")
                {
                    idx -= 1;
                    single_mul = true;
                } //849 (= (* lam6n64 rfc9) 0) now the idx at second '('
                for(;idx<vec.size();idx++)
                {
                    //(* 50001 lam102n0)
                    //(* (- 1) lam101n6)
                    //(* Nl2main_z1 lam101n12)
                    //(* (- 1) (* Nl2main_x1 lam10n12))
                    //8 (= 0 (+ lam4n0 (* (- 1) Nl2main_x2)))
                    //849 (= 0 (* lam6n64 rfc9))
                    if(idx==vec.size()-1)
                    {
                        //To be check :
                        //在vec小于5的里面，也有可能系数是负的，也有可能系数在前面
                        //小于5的里面check一下not的，然后总体check一遍 
                        //check single_mul
                        if(!is_key_neg)  l->key = -std::atoll(delete_pa(vec[idx]).c_str());//如果判定号是等号,那么系数有可能在前面 //849 (= 0 (* lam6n64 rfc9))
                        else l->key=std::atoll(delete_pa(vec[idx]).c_str());
                        if (is_gt==1)
                        {
                            l->key++;
                            invert_lit(*l);
                        }
                        break;
                    }
                    else if(vec[idx]=="(-")
                    {
                        is_key_neg=true;
                    }
                    else if (vec[idx] == "(*")
                    {
                        idx += 1;
                        term new_t;
                        if ((vec[idx][0] < '0' || vec[idx][0] > '9') && (vec[idx] != "(-"))
                        { //(* Nl2main_z1 lam101n12)
                        //(* undef62256 (+ Nl186var_Le_AFp_4___rho_1_^01 Nl186var_e_EFAFp_0___rho_1_^01))
                        //(* undef94 (+ (* (- 1) Nl5arg21) (* (- 1) Nl5arg41) (* (- 1) Nl5arg61)))) 0)
                        //(* arg7 (+ (* 2 Nl5arg73) Nl5arg83))
                        //这里没考虑负号和系数，明天加一下
                        //(* var_e_EFAFp_0___rho_2_^0 (+ Nl186var_Le_AFp_4___rho_2_^01 Nl186var_e_EFAFp_0___rho_2_^01))
                            if(idx+1<=vec.size()-1&&vec[idx+1]=="(+")
                            {
                                var_exp first((int)transfer_name_to_tmp_var(vec[idx]));
                                idx+=2;
                                while(true)
                                {
                                    term new_t_special;
                                    new_t_special.var_epxs.push_back(first);
                                    if(vec[idx]=="(*" && vec[idx+1] =="(-")
                                    {
                                        idx++;
                                        __int128_t coff = -std::atoll(delete_pa(vec[++idx]).c_str());
                                        std::string cur_var=delete_pa(vec[++idx]);
                                        var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                        new_t_special.var_epxs.push_back(ve);
                                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_special), coff));
                                    }
                                    else if(vec[idx]=="(*" && is_Number(vec[idx+1]) )
                                    {
                                        __int128_t coff = std::atoll(delete_pa(vec[++idx]).c_str());
                                        std::string cur_var=delete_pa(vec[++idx]);
                                        var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                        new_t_special.var_epxs.push_back(ve);
                                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_special), coff));
                                    }
                                    else if(!is_Number(vec[idx]))
                                    {
                                        std::string cur_var=delete_pa(vec[idx]);
                                        var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                        new_t_special.var_epxs.push_back(ve);
                                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_special), 1));
                                    }
                                    if(count(vec[idx].begin(),vec[idx].end(),')')>=2) break;
                                    else idx++;
                                }
                                // while(!is_pa(vec[idx]))
                                // {
                                //     term new_t_special;
                                //     var_exp ve((int)transfer_name_to_tmp_var(vec[idx++]));
                                //     new_t_special.var_epxs.push_back(first);
                                //     l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_special), 1));
                                // }
                                // term new_t_special_2;
                                // std::string cur_var=delete_pa(vec[idx]);
                                // var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                // new_t_special_2.var_epxs.push_back(first);
                                // new_t_special_2.var_epxs.push_back(ve);
                                // l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_special_2), 1));
                            }
                            else
                            {
                                while (!is_pa(vec[idx]))
                                {
                                    var_exp ve((int)transfer_name_to_tmp_var(vec[idx++]));
                                    new_t.var_epxs.push_back(ve);
                                }
                                std::string cur_var=delete_pa(vec[idx]);
                                var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                                new_t.var_epxs.push_back(ve);
                                l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                            }
                        }
                        else if((vec[idx]== "(-")&&(vec[idx+2][0] < '0' || vec[idx+2][0] > '9'))
                        {   //(* (- 1) lam101n6)
                            __int128_t coff = -std::atoll(delete_pa(vec[++idx]).c_str());
                            std::string cur_var=delete_pa(vec[++idx]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                        }
                        else if((vec[idx]== "(-")&&vec[idx+2]=="(*")
                        {   //(* (- 1) (* Nl2main_x1 lam10n12))
                            __int128_t coff = -std::atoll(delete_pa(vec[++idx]).c_str());
                            idx+=2;
                            while (!is_pa(vec[idx]))
                            {
                                var_exp ve((int)transfer_name_to_tmp_var(vec[idx++]));
                                new_t.var_epxs.push_back(ve);
                            }
                            std::string cur_var=delete_pa(vec[idx]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                        else
                        {   //(* 50001 lam102n0)
                            __int128_t coff = std::atoll(vec[idx++].c_str());
                            std::string cur_var=delete_pa(vec[idx]);
                            var_exp ve((int)transfer_name_to_tmp_var(cur_var));
                            new_t.var_epxs.push_back(ve);
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), coff));
                        }
                        if (single_mul)
                        {
                            break;//to be checked
                        } // now the idx at ')'
                    }
                    else
                    {
                        term new_t;
                        std::string cur_var=delete_pa(vec[idx]);
                        new_t.var_epxs.push_back(var_exp((int)transfer_name_to_tmp_var(cur_var)));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                    }
                }
            }
            else 
            {
                l->is_nia_lit=true;
                l->is_soft=1;
                term new_t;
                if (vec[1].find("bool")!=std::string::npos)
                {
                    l->delta = transfer_name_to_resolution_var(vec[1], false);
                    l->key = 1;
                    l->is_nia_lit = false;
                }
                else if (vec[1] == "(not")
                {
                    l->is_not=1;//if 条件有问题
                    if (vec[2] == "(=" && vec.size() == 5 && (vec[3][0] < '0' || vec[3][0] > '9') && (vec[4][0] < '0' || vec[4][0] > '9') && (vec[3] != "(-") && (vec[4] != "(-"))
                    {
                        // std::cout<<"here1"<<std::endl;
                        l->is_equal = true;
                        l->key = 0;
                        term new_t_1, new_t_2;
                        std::string var_name=delete_pa(vec[4]);
                        var_exp ve_1((int)transfer_name_to_tmp_var(vec[3])), ve_2((int)transfer_name_to_tmp_var(var_name));
                        new_t_1.var_epxs.push_back(ve_1);
                        new_t_2.var_epxs.push_back(ve_2);
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_1), 1));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_2), -1));
                    } //20 (not (= x1 x2))
                    else
                    {
                        __int128_t bound;
                        uint64_t var_idx;
                        if ((vec[3][0] < '0' || vec[3][0] > '9') && (vec[3]!= "(-"))
                        {
                            // std::cout<<"here2"<<std::endl;
                            if(vec[4]=="(-")  bound = -std::atoll(delete_pa(vec[5]).c_str());
                            else  bound = std::atoll(delete_pa(vec[4]).c_str());
                            var_idx = transfer_name_to_tmp_var(vec[3]);
                        } //20 (not (>= lam5n0 0)) //20 (not (>= xH457 (- 250)))
                        else if((vec[4][0] < '0' || vec[4][0] > '9') && (vec[4] != "(-"))
                        {
                            // std::cout<<"here3"<<std::endl;
                            int idx=4;
                            if(vec[3]=="(-")  {bound = -std::atoll(delete_pa(vec[4]).c_str());idx++;}
                            else  bound = std::atoll(delete_pa(vec[3]).c_str());
                            std::string var_name=delete_pa(vec[idx]);
                            var_idx = transfer_name_to_tmp_var(var_name);
                        } //6 (not (= 0 x)) //6 (not (= (- 100) x))
                        term new_t;
                        new_t.var_epxs.push_back(var_exp((int)var_idx));
                        if (vec[2] == "(>=")
                        {
                            l->key = bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                        }
                        else
                        {
                            l->key = -bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                        l->is_equal = (vec[2] == "(=");
                    }
                }
                else 
                {
                    
                    if (vec[1] == "(=" && vec.size() == 4 && (vec[2][0] < '0' || vec[2][0] > '9') && (vec[3][0] < '0' || vec[3][0] > '9') && (vec[2] != "(-") && (vec[3] != "(-"))
                    {
                        l->is_equal = true;
                        l->key = 0;
                        term new_t_1, new_t_2;
                        std::string var_name=delete_pa(vec[3]);
                        var_exp ve_1((int)transfer_name_to_tmp_var(vec[2])), ve_2((int)transfer_name_to_tmp_var(var_name));
                        new_t_1.var_epxs.push_back(ve_1);
                        new_t_2.var_epxs.push_back(ve_2);
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_1), 1));
                        l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t_2), -1));
                    } //20 (= x1 x2)
                    else
                    {
                        __int128_t bound;
                        uint64_t var_idx;
                        if ((vec[2][0] < '0' || vec[2][0] > '9') && (vec[2]!= "(-"))
                        {
                            if(vec[3]=="(-")  bound = -std::atoll(delete_pa(vec[4]).c_str());
                            else  bound = std::atoll(delete_pa(vec[3]).c_str());
                            var_idx = transfer_name_to_tmp_var(vec[2]);
                        } //20 (not (>= lam5n0 0)) //20 (not (>= xH457 (- 250)))
                        else if((vec[3][0] < '0' || vec[3][0] > '9') && (vec[3] != "(-"))
                        {
                            int idx=3;
                            if(vec[2]=="(-")  {bound = -std::atoll(delete_pa(vec[3]).c_str());idx++;}
                            else  bound = std::atoll(delete_pa(vec[2]).c_str());
                            std::string var_name=delete_pa(vec[idx]);
                            var_idx = transfer_name_to_tmp_var(var_name);
                        } //6 (= 0 x)) //6 (not (= (- 100) x))
                        term new_t;
                        new_t.var_epxs.push_back(var_exp((int)var_idx));
                        if (vec[1] == "(>=")
                        {
                            l->key = bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
                        }
                        else
                        {
                            l->key = -bound;
                            l->coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
                        }
                        l->is_equal = (vec[1] == "(=");
                    }
                }
            }
        }
        getline(std::cin,in_string);
        int new_hard_clause_num=stoi(in_string);
        //传递硬子句
        for(int i=0;i<new_hard_clause_num;i++)
        {
            getline(std::cin,in_string);
            std::vector<std::string> vec;
            split_string(in_string, vec);
            std::vector<int> cur_clause;
            for(int j=0;j<vec.size();j++)
            {
                if(vec[j]=="") continue;
                int index=stoi(vec[j]);
                int real_index=org_num+abs(index)-1;
                bool not_flag,not_flag_2;
                if( (index<0) ^ (_lits[real_index].is_not==1) ) not_flag=1;
                else not_flag=0;
                if(not_flag) cur_clause.push_back(-real_index);//处理not
                else cur_clause.push_back(real_index);
            }
            new_hard_clauses.push_back(cur_clause);
        }
        getline(std::cin,in_string);
        //传递唯一为真的硬子句本来的权重
        pseudo_hard_clause_weight=stoi(in_string);
        fclose(stdin);
        // for(int i=0;i<_num_lits;i++)
        // {
        //     print_literal(_lits[i]);
        // }
        // exit(0);
        return is_or_hard;
        // for(int i=0;i<soft_clauses_weight.size();i++)
        // {
        //     std::cout<<_soft_clauses[i].org_weight<<std::endl;
        // }
        // exit(0);
        // std::cout<<_num_lits<<std::endl;
    }

    int ls_solver::find(int var_idx)
    {
        if (var_idx == fa[var_idx])
        {
            fa_coff[var_idx] = 1;
            return var_idx;
        }
        else
        {
            int old_fa = fa[var_idx];
            int new_fa = find(fa[var_idx]);
            fa_coff[var_idx] *= fa_coff[old_fa];
            return fa[var_idx] = new_fa;
        }
    }

    void ls_solver::merge(int var_idx_1, int var_idx_2, int coff_1, int coff_2)
    { // coff_1*var_1==coff_2*var_2
        // std::cout<<"merge"<<std::endl;
        int fa_1 = find(var_idx_1), fa_2 = find(var_idx_2);
        if (fa_1 == fa_2)
        {
            return;
        }
        int fa_coff_1 = fa_coff[var_idx_1] * coff_1, fa_coff_2 = fa_coff[var_idx_2] * coff_2; // fa_coff_1*fa_1=fa_coff_2*fa_2
        if ((std::abs(fa_coff_1) > std::abs(fa_coff_2) && fa_coff_1 % fa_coff_2 == 0) || (std::abs(fa_coff_2) == std::abs(fa_coff_1) && fa_1 < fa_2))
        {
            fa[fa_2] = fa_1;
            fa_coff[fa_2] = fa_coff_1 / fa_coff_2;
        } // fa_2=(fa_coff_1/fa_coff_2)*fa_1
        else if ((std::abs(fa_coff_2) > std::abs(fa_coff_1) && fa_coff_2 % fa_coff_1 == 0) || (std::abs(fa_coff_2) == std::abs(fa_coff_1) && fa_2 < fa_1))
        {
            fa[fa_1] = fa_2;
            fa_coff[fa_1] = fa_coff_2 / fa_coff_1;
        } // fa_1=(fa_coff_2/fa_coff_1)*fa_2
    }
    bool cmp_coff_term(coff_term cf1, coff_term cf2) { return cf1.term_idx < cf2.term_idx; }
    void ls_solver::equal_vars(std::vector<std::vector<int>> &clause_vec)
    {
        fa.resize(_tmp_vars.size());
        for (int var_idx = 0; var_idx < _tmp_vars.size(); var_idx++)
        {
            fa[var_idx] = var_idx;
        } // initialize the fa vec
        fa_coff.resize(_tmp_vars.size(), 1);
        std::vector<int> unit_equal_lits;
        // find out all unit equal lits
        for (int clause_idx = 0; clause_idx < clause_vec.size(); clause_idx++)
        {
            if (clause_vec[clause_idx].size() == 1 && clause_vec[clause_idx][0] > 0)
            {
                int lit_idx = clause_vec[clause_idx][0];
                lit *l = &(_lits[lit_idx]);
                if (l->key == 0 && l->is_equal)
                { // t1+t2+..+tn=0
                    bool flag_all_single = true;
                    for (coff_term &cf : l->coff_terms)
                    {
                        if (!is_single_var_term(_terms[cf.term_idx]))
                        {
                            flag_all_single = false;
                            break;
                        }
                    }
                    if (flag_all_single)
                    {
                        unit_equal_lits.push_back(lit_idx);
                    }
                }
            }
        }
        bool find_new_merge = true;
        while (find_new_merge)
        {
            find_new_merge = false;
            // merge the equalities
            for (int i = 0; i < unit_equal_lits.size(); i++)
            {
                lit *l = &(_lits[unit_equal_lits[i]]);
                if (l->lits_index == 0)
                {
                    continue;
                }
                if (l->coff_terms.size() == 2)
                {
                    find_new_merge = true;
                    int var_1 = _terms[l->coff_terms[0].term_idx].var_epxs[0].var_index;
                    int var_2 = _terms[l->coff_terms[1].term_idx].var_epxs[0].var_index;
                    // std::cout<<"merge: "<<var_1<<"  "<<var_2<<std::endl;
                    merge(var_1, var_2, l->coff_terms[0].coff, -l->coff_terms[1].coff);//(5x1 -2x1 )
                    l->lits_index = 0;
                }
            }
            // modify the lit by new equality
            for (int i = 0; i < unit_equal_lits.size(); i++)
            {
                update_lit_equal(unit_equal_lits[i]);
            }
        }
        //    std::cout<<"eq map\n";
        //    for(int v_idx=0;v_idx<_tmp_vars.size();v_idx++){
        //        int new_v_idx=find(v_idx);
        //        if(new_v_idx!=v_idx){
        //            std::cout<<_tmp_vars[v_idx].var_name<<" = "<<fa_coff[v_idx]<<" * "<<_tmp_vars[new_v_idx].var_name<<"\n";
        //        }
        //    }
        // update all lits
        for (int lit_idx = 0; lit_idx < _lits.size(); lit_idx++)
        {
            update_lit_equal(lit_idx);//单元消解了x=3y这种单元lit，有的lit coffterm变成了0
        }
        // for(int i=0;i<_num_lits;i++)
        // {
        //     print_literal(_lits[i]);
        // }
        // exit(0);
    }

    void ls_solver::update_lit_equal(int lit_idx)
    {
        lit *l = &(_lits[lit_idx]);
        if (l->lits_index == 0 || !l->is_nia_lit)
        {
            return;//这里去掉了addition len
        }
        bool lit_modified = false;
        for (coff_term &cf : l->coff_terms)
        {
            term new_t = _terms[cf.term_idx];
            bool term_modified = false;
            int new_coff = cf.coff;
            for (var_exp &ve : new_t.var_epxs)
            {
                int var_idx = ve.var_index;
                int new_var_idx = find(var_idx);
                if (new_var_idx != var_idx)
                { // modify the var
                    lit_modified = true;
                    term_modified = true;
                    ve.var_index = new_var_idx;
                    new_coff *= fa_coff[var_idx];
                }
            }
            if (term_modified)
            {
                cf = coff_term((int)transfer_term_to_idx(new_t), new_coff);//把对应变量替换过来
            }
        }
        if (lit_modified)
        {
            std::sort(l->coff_terms.begin(), l->coff_terms.end(), cmp_coff_term);
            int curr_term_idx = l->coff_terms[0].term_idx;
            int curr_coff = 0;
            int lit_coff_term_idx = 0;
            for (int cf_idx = 0; cf_idx < l->coff_terms.size(); cf_idx++)
            {
                if (l->coff_terms[cf_idx].term_idx != curr_term_idx)
                {
                    curr_term_idx = l->coff_terms[cf_idx].term_idx;
                    curr_coff = 0;
                }                                        // enter a new term
                curr_coff += l->coff_terms[cf_idx].coff; // the same term
                if (curr_coff!=0 && (cf_idx == l->coff_terms.size() - 1 || l->coff_terms[cf_idx + 1].term_idx != curr_term_idx))
                {
                    l->coff_terms[lit_coff_term_idx].term_idx = curr_term_idx;
                    l->coff_terms[lit_coff_term_idx++].coff = curr_coff;
                } // the last coff_term of the current term
            }
            l->coff_terms.resize(lit_coff_term_idx);//这里有可能是0?
            if(lit_coff_term_idx==0) l->lits_index=0;
        }
    }

    void ls_solver::build_instance(std::vector<std::vector<int>> &clause_vec)
    {
        equal_vars(clause_vec);
        //到这的逻辑是对的！
        for (int clause_idx = 0; clause_idx < clause_vec.size(); clause_idx++)
        {
            if (clause_vec[clause_idx].size() == 1)
            {
                lit *l = &(_lits[std::abs(clause_vec[clause_idx][0])]);
                if (l->is_equal || !l->is_nia_lit)
                {
                    continue;
                } // equal lit is not bound lit
                if (l->coff_terms.size() == 1 && is_single_var_term(_terms[l->coff_terms[0].term_idx]))
                {
                    __int128_t new_low_bound = -max_int;
                    __int128_t new_upper_bound = max_int;
                    int var_idx = _terms[l->coff_terms[0].term_idx].var_epxs[0].var_index;
                    if (clause_vec[clause_idx][0] > 0)
                    {
                        if (l->coff_terms[0].coff > 0)
                        {
                            new_upper_bound = devide((-l->key), (l->coff_terms[0].coff));
                        } // ax+k<=0   x<=(-k/a)
                        else
                        {
                            new_low_bound = devide((-l->key), (l->coff_terms[0].coff));
                        } // ax+k<=0  x>=(-k/a)
                    }
                    else
                    {
                        if (l->coff_terms[0].coff > 0)
                        {
                            new_low_bound = devide((1 - l->key), (l->coff_terms[0].coff));
                        } // ax+k>0 ax+k>=1 x>=(1-k)/a
                        else
                        {
                            new_upper_bound = devide((1 - l->key), (l->coff_terms[0].coff));
                        } // ax+k>=1 x<=(1-k)/a
                    }
                    if (new_low_bound > _tmp_vars[var_idx].low_bound)
                    {
                        _tmp_vars[var_idx].low_bound = new_low_bound;
                    }
                    else if (new_upper_bound < _tmp_vars[var_idx].upper_bound)
                    {
                        _tmp_vars[var_idx].upper_bound = new_upper_bound;
                    }
                    if (l->lits_index != 0)
                    {
                        _bound_lits.push_back(l->lits_index);
                    }
                    _bound_clauses.push_back(clause_vec[clause_idx][0]);
                    // l->lits_index = 0;
                    // if (clause_vec[clause_idx][0] < 0)
                    // {
                    //     clause_vec[clause_idx][0] = -clause_vec[clause_idx][0];
                    // }
                }
            }
        }
        reduce_vars();
        // exit(0);
        _clauses.resize(clause_vec.size());
        _num_clauses = 0;
        for (auto clause_curr : clause_vec)
        {
            bool is_tautology = false;
            for (auto l_idx : clause_curr)
            {
                if (_lits[std::abs(l_idx)].lits_index == 0)
                {
                    is_tautology = true;
                    break;
                }
                if(_lits[std::abs(l_idx)].lits_index == -2&&l_idx>0 ||_lits[std::abs(l_idx)].lits_index == -1&&l_idx<0)
                {
                    is_tautology = true;
                    break;
                }
            }
            if (is_tautology)
            {
                continue;
            }
            for (auto l_idx : clause_curr)
            {
                if(_lits[std::abs(l_idx)].lits_index == -2&&l_idx<0 ||_lits[std::abs(l_idx)].lits_index == -1&&l_idx>0)
                {
                    continue;
                }
                _clauses[_num_clauses].literals.push_back(l_idx);
                lit *l = &(_lits[std::abs(l_idx)]);
                if (l->lits_index == 0)
                {
                    continue;
                }
                if (!l->is_nia_lit)
                {
                    _resolution_vars[l->delta].clause_idxs.push_back((int)_num_clauses);
                }
            }
            _num_clauses++;
        }
        _clauses.resize(_num_clauses);
        // now the vars are all in the resolution vars
        unit_prop();
        resolution();
        unit_prop();
        // exit(0);
        reduce_clause();
        //    print_formula();
        best_found_cost = (int)_num_clauses;
        make_space();
        set_pre_value();
        // exit(0);
    }

    // return the index of a term if it exists, otherwise create a new one
    uint64_t ls_solver::transfer_term_to_idx(term t)
    {
        std::string term_str;
        transfer_term_to_str(t, term_str);
        if (str2termidx.find(term_str) == str2termidx.end())
        {
            str2termidx[term_str] = _terms.size();
            _terms.push_back(t);
            return _terms.size() - 1;
        }
        else
            return str2termidx[term_str];
    }
    bool cmp_ve(var_exp ve1, var_exp ve2)
    {
        return (ve1.exponent < ve2.exponent) || (ve1.exponent == ve2.exponent && ve1.var_index < ve2.var_index);
    }

    // sort the term var_index and the exponent
    void ls_solver::transfer_term_to_str(term &t, std::string &str)
    {
        std::sort(t.var_epxs.begin(), t.var_epxs.end(), cmp_ve);
        str.clear();
        for (int i = 0; i < t.var_epxs.size(); i++)
        {
            str += "_" + std::to_string(t.var_epxs[i].var_index) + "^" + std::to_string(t.var_epxs[i].exponent);
        }
    }

    uint64_t ls_solver::transfer_name_to_reduced_var(std::string &name, bool is_nia)
    {
        if (name2var.find(name) == name2var.end())
        {
            name2var[name] = _vars.size();
            variable var;
            var.var_name = name;
            var.is_nia = is_nia;
            _vars.push_back(var);
            if (is_nia)
            {
                nia_var_vec.push_back((int)_vars.size() - 1);
            }
            else
            {
                bool_var_vec.push_back((int)_vars.size() - 1);
            }
            return _vars.size() - 1;
        }
        else
            return name2var[name];
    }

    uint64_t ls_solver::transfer_name_to_resolution_var(std::string &name, bool is_nia)
    {
        if (name2resolution_var.find(name) == name2resolution_var.end())
        {
            name2resolution_var[name] = _resolution_vars.size();
            variable var;
            var.clause_idxs.reserve(64);
            var.literal_idxs.reserve(64);
            var.term_idxs.reserve(64);
            var.var_lit_terms.reserve(64);
            var.var_name = name;
            var.is_nia = is_nia;
            _resolution_vars.push_back(var);
            if (is_nia)
            {
                nia_var_vec.push_back((int)_resolution_vars.size() - 1);
            }
            else
            {
                bool_var_vec.push_back((int)_resolution_vars.size() - 1);
            }
            return _resolution_vars.size() - 1;
        }
        else
            return name2resolution_var[name];
    }

    uint64_t ls_solver::transfer_name_to_tmp_var(std::string &name)
    {
        if (name2tmp_var.find(name) == name2tmp_var.end())
        {
            name2tmp_var[name] = _tmp_vars.size();
            variable var;
            var.is_nia = true;
            var.var_name = name;
            _tmp_vars.push_back(var);
            return _tmp_vars.size() - 1;
        }
        else
            return name2tmp_var[name];
    }
    // transfer the nia var into _resolution_vars, turn (x-y) to z
    void ls_solver::reduce_vars()
    {
        const uint64_t tmp_vars_size = _tmp_vars.size();
        std::vector<int> hash_map(tmp_vars_size * tmp_vars_size, 0); // hash_map[A*(size)+b]=n means A-B has occurred n times
        std::vector<int> occur_time(tmp_vars_size, 0);               // occur_time[a]=n means that a has occured in lits for n times
        term *t;
        variable *original_var;
        variable *new_var;
        std::string var_name;
        int original_var_idx;
        use_pbs = !(_resolution_vars.size() == 0);
        for (int var_idx = 0; var_idx < tmp_vars_size; var_idx++)
        {
            if (_tmp_vars[var_idx].upper_bound > 1 || _tmp_vars[var_idx].low_bound < 0)
            {
                use_pbs = false;
                break;
            }
        }
        if (use_pbs)
        {
            _resolution_vars = _tmp_vars;
        } // if there is no boolean vars and all nia vars are in [0,1], then use pbs, and no need to reduce the vars
        else
        {
            name2var.clear();
            str2termidx.clear();
            // rewrite terms, and put all integer vars into resolution_vars, map the term to number again
            for (int term_idx = 0; term_idx < _terms.size(); term_idx++)
            {
                t = &(_terms[term_idx]);
                for (int ve_idx = 0; ve_idx < t->var_epxs.size(); ve_idx++)
                {
                    original_var_idx = t->var_epxs[ve_idx].var_index;
                    t->var_epxs[ve_idx].var_index = (int)transfer_name_to_resolution_var(_tmp_vars[original_var_idx].var_name, true);
                }
                std::string term_s;
                transfer_term_to_str(*t, term_s);
                str2termidx[term_s] = term_idx;
            }
            std::string term_s;
            for (int term_idx = 0; term_idx < _terms.size(); term_idx++)
            {
                transfer_term_to_str(_terms[term_idx], term_s);
                str2termidx[term_s] = term_idx;//重复的逻辑？
            }
            // set low and upbound
            for (original_var_idx = 0; original_var_idx < _tmp_vars.size(); original_var_idx++)
            {
                original_var = &(_tmp_vars[original_var_idx]);
                // original var
                new_var = &(_resolution_vars[transfer_name_to_resolution_var(original_var->var_name, true)]);
                new_var->low_bound = original_var->low_bound;
                new_var->upper_bound = original_var->upper_bound;
            }
        }
        variable *cur;
        lit *l;
        term new_t;
        for (uint64_t lit_i = 0; lit_i < _bound_lits.size(); lit_i++)
        {
            l = &_lits[(_bound_lits[lit_i])];
            if (l->coff_terms[0].coff < 0)
            {
                new_t=_terms[l->coff_terms[0].term_idx];
                cur = &(_resolution_vars[new_t.var_epxs[0].var_index]);
                if (cur->low_bound != -max_int && cur->upper_bound != max_int)
                {
                    if(_bound_clauses[lit_i]>0)
                        l->lits_index = -2;
                    else l->lits_index=-1;
                }
                else
                {
                    cur->low_bound = -max_int;
                    cur->upper_bound = max_int;
                }
            }
            else if (l->coff_terms[0].coff > 0)
            {
                new_t=_terms[l->coff_terms[0].term_idx];
                cur = &(_resolution_vars[new_t.var_epxs[0].var_index]);
                if (cur->low_bound != -max_int && cur->upper_bound != max_int)
                {
                    if(_bound_clauses[lit_i]>0)
                        l->lits_index = -2;
                    else l->lits_index=-1;
                }
                else
                {
                    cur->low_bound = -max_int;
                    cur->upper_bound = max_int;
                }
            }
        }
        // int num_var_with_bound = 0;
        // for (int var_idx = 0; var_idx < _resolution_vars.size(); var_idx++)
        // {
        //     new_var = &(_resolution_vars[var_idx]);
        //     if (!new_var->is_nia)
        //     {
        //         continue;
        //     }
        //     if (new_var->upper_bound != max_int && new_var->low_bound != -max_int)
        //     {
        //         continue;
        //     } // if a var has both upper bound and lower bound, no bound lits is added.
        //     if (new_var->low_bound != -max_int)
        //     {
        //         int lit_idx = _bound_lits[num_var_with_bound++];
        //         lit bound_lit;
        //         bound_lit.is_nia_lit = true;
        //         bound_lit.lits_index = lit_idx;
        //         term new_t;
        //         new_t.var_epxs.push_back(var_idx);
        //         bound_lit.coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), -1));
        //         bound_lit.key = new_var->low_bound;
        //         _lits[lit_idx] = bound_lit;
        //         new_var->low_bound = -max_int;
        //     }
        //     if (new_var->upper_bound != max_int)
        //     {
        //         int lit_idx = _bound_lits[num_var_with_bound++];
        //         lit bound_lit;
        //         bound_lit.is_nia_lit = true;
        //         bound_lit.lits_index = lit_idx;
        //         term new_t;
        //         new_t.var_epxs.push_back(var_idx);
        //         bound_lit.coff_terms.push_back(coff_term((int)transfer_term_to_idx(new_t), 1));
        //         bound_lit.key = -new_var->upper_bound;
        //         _lits[lit_idx] = bound_lit;
        //         new_var->upper_bound = max_int;
        //     }
        // }
    }

    void ls_solver::unit_prop()
    {
        std::stack<uint64_t> unit_clause; // the var_idx in the unit clause
        for (uint64_t clause_idx = 0; clause_idx < _num_clauses; clause_idx++)
        { // the unit clause is the undeleted clause containing only one bool var
            if (!_clauses[clause_idx].is_delete && _clauses[clause_idx].literals.size() == 1 && !_lits[std::abs(_clauses[clause_idx].literals[0])].is_nia_lit)
            {
                unit_clause.push(clause_idx);
            }
        }
        while (!unit_clause.empty())
        {
            uint64_t unit_clause_idx = unit_clause.top();
            unit_clause.pop();
            if (_clauses[unit_clause_idx].is_delete)
            {
                continue;
            }
            int is_pos_lit = (_clauses[unit_clause_idx].literals[0] > 0) ? 1 : -1;            // determine the sign of the var in unit clause
            uint64_t unit_var = _lits[std::abs(_clauses[unit_clause_idx].literals[0])].delta; // determing the var in unit clause
            _resolution_vars[unit_var].is_delete = true;                                      // delete the unit var
            _resolution_vars[unit_var].up_bool = is_pos_lit;                                  // set the solution of a boolean var as its unit propogation value
            for (uint64_t cl_idx : _resolution_vars[unit_var].clause_idxs)
            {
                clause *cl = &(_clauses[cl_idx]);
                if (cl->is_delete)
                    continue;
                for (uint64_t lit_idx = 0; lit_idx < cl->literals.size(); lit_idx++)
                {
                    int l_id_in_lits = cl->literals[lit_idx];
                    lit *l = &(_lits[std::abs(l_id_in_lits)]);
                    if (!l->is_nia_lit && l->delta == unit_var)
                    { // go through the clauses of the unit var, find the var in corresponding clause
                        if ((is_pos_lit > 0 && l_id_in_lits > 0) || (is_pos_lit < 0 && l_id_in_lits < 0))
                        {
                            cl->is_delete = true;
                            for (int l_idx_inner : cl->literals)
                            { // delete the clause from corresponding bool var
                                lit *l_inner = &(_lits[std::abs(l_idx_inner)]);
                                if (!l_inner->is_nia_lit && l_inner->delta != unit_var)
                                {
                                    variable *var_inner = &(_resolution_vars[l_inner->delta]);
                                    for (uint64_t delete_idx = 0; delete_idx < var_inner->clause_idxs.size(); delete_idx++)
                                    {
                                        if (var_inner->clause_idxs[delete_idx] == cl_idx)
                                        {
                                            var_inner->clause_idxs[delete_idx] = var_inner->clause_idxs.back();
                                            var_inner->clause_idxs.pop_back();
                                            break;
                                        }
                                    }
                                }
                            }
                        } // if there exist same lit, the clause is already set true, then delete the clause
                        else
                        { // else delete the lit
                            cl->literals[lit_idx] = cl->literals.back();
                            cl->literals.pop_back();
                            if (cl->literals.size() == 1 && !_lits[std::abs(cl->literals[0])].is_nia_lit)
                            {
                                unit_clause.push(cl_idx);
                            } // if after deleting, it becomes unit clause
                        }
                        break;
                    }
                }
            }
        }
    }
    __int128_t ls_solver::hash_lits_to_num(std::vector<int> &lits)
    {
        std::sort(lits.begin(), lits.end());
        __int128_t hash_num = 0;
        for (int lit_idx : lits)
        {
            hash_num = (__int128_t)hash_num * (__int128_t)(_num_lits) + (__int128_t)lit_idx + (__int128_t)_num_lits;
        }
        return hash_num;
    }
    bool ls_solver::is_same_lits(std::vector<int> &lits_1, std::vector<int> &lits_2)
    {
        if (lits_1.size() != lits_2.size())
        {
            return false;
        }
        std::sort(lits_1.begin(), lits_1.end());
        std::sort(lits_2.begin(), lits_2.end());
        for (int l_idx = 0; l_idx < lits_1.size(); l_idx++)
        {
            if (lits_1[l_idx] != lits_2[l_idx])
            {
                return false;
            }
        }
        return true;
    }

    void ls_solver::resolution()
    {
        std::vector<uint64_t> pos_clauses(10 * _num_clauses);
        std::vector<uint64_t> neg_clauses(10 * _num_clauses);
        std::map<__int128_t, int> clauselit_map;            // for the clause with literal {a,b,c}, sort the lit by its order, and hash the literals to a number, then map it to the clause_idx, if deleted, set it to -1
        std::vector<__int128_t> clauselit(_clauses.size()); // hash the lits of clause to a number
        for (int cls_idx = 0; cls_idx < _clauses.size(); cls_idx++)
        {
            clauselit[cls_idx] = hash_lits_to_num(_clauses[cls_idx].literals);
            clauselit_map[clauselit[cls_idx]] = cls_idx;
        }
        int pos_clause_size, neg_clause_size;
        bool is_improve = true;
        while (is_improve)
        {
            is_improve = false;
            for (uint64_t bool_var_idx : bool_var_vec)
            {
                if (_resolution_vars[bool_var_idx].is_delete)
                    continue;
                pos_clause_size = 0;
                neg_clause_size = 0;
                for (int i = 0; i < _resolution_vars[bool_var_idx].clause_idxs.size(); i++)
                {
                    uint64_t clause_idx = _resolution_vars[bool_var_idx].clause_idxs[i];
                    if (_clauses[clause_idx].is_delete)
                        continue;
                    for (int l_var_sign : _clauses[clause_idx].literals)
                    {
                        if (!_lits[std::abs(l_var_sign)].is_nia_lit && _lits[std::abs(l_var_sign)].delta == bool_var_idx)
                        { // make sure that it is a boolean literal and is exactly the one containing the var
                            if (l_var_sign > 0)
                            {
                                pos_clauses[pos_clause_size++] = clause_idx;
                            }
                            else
                            {
                                neg_clauses[neg_clause_size++] = clause_idx;
                            }
                            break;
                        }
                    }
                } // determine the pos_clause and neg_clause
                int tautology_num = 0;
                for (int i = 0; i < pos_clause_size; i++)
                { // pos clause X neg clause
                    uint64_t pos_clause_idx = pos_clauses[i];
                    for (int j = 0; j < neg_clause_size; j++)
                    {
                        uint64_t neg_clause_idx = neg_clauses[j];
                        for (int k = 0; k < _clauses[neg_clause_idx].literals.size(); k++)
                        {
                            int l_neg_lit = _clauses[neg_clause_idx].literals[k];
                            if (_lits[std::abs(l_neg_lit)].delta != bool_var_idx || _lits[std::abs(l_neg_lit)].is_nia_lit)
                            { // the bool_var for resolution is not considered(that is \neg ( the lit is bool lit and it contains the var))
                                for (int l_pos_lit : _clauses[pos_clause_idx].literals)
                                {
                                    if (-l_neg_lit == (l_pos_lit))
                                    {
                                        tautology_num++;
                                        break;
                                    } // if there exists (aVb)^(-aV-b), the new clause is tautology
                                }
                            }
                        }
                    }
                }
                if ((pos_clause_size * neg_clause_size - tautology_num) > (pos_clause_size + neg_clause_size))
                {
                    continue;
                } // if deleting the var can cause 2 times clauses, then skip it
                for (uint64_t clause_idx : _resolution_vars[bool_var_idx].clause_idxs)
                { // delete the clauses of bool_var
                    _clauses[clause_idx].is_delete = true;
                    for (int l_idx_sign : _clauses[clause_idx].literals)
                    { // delete the clause from corresponding bool var
                        lit *l = &(_lits[std::abs(l_idx_sign)]);
                        if (!l->is_nia_lit && l->delta != bool_var_idx)
                        {
                            variable *var_inner = &(_resolution_vars[l->delta]);
                            for (uint64_t delete_idx = 0; delete_idx < var_inner->clause_idxs.size(); delete_idx++)
                            {
                                if (var_inner->clause_idxs[delete_idx] == clause_idx)
                                {
                                    var_inner->clause_idxs[delete_idx] = var_inner->clause_idxs.back();
                                    var_inner->clause_idxs.pop_back();
                                    break;
                                }
                            }
                        }
                    }
                }
                is_improve = true;
                _resolution_vars[bool_var_idx].is_delete = true;
                if (pos_clause_size == 0)
                {
                    _resolution_vars[bool_var_idx].up_bool = -1;
                } // if it is a false pure lit, the var is set to false
                if (neg_clause_size == 0)
                {
                    _resolution_vars[bool_var_idx].up_bool = 1;
                } // if it is a true pure lit, the var is set to true
                if (pos_clause_size == 0 || neg_clause_size == 0)
                    continue; // pos or neg clause is empty, meaning the clauses are SAT when assigned to true or false, then cannot resolute, just delete the clause
                for (int i = 0; i < pos_clause_size; i++)
                { // pos clause X neg clause
                    uint64_t pos_clause_idx = pos_clauses[i];
                    for (int j = 0; j < neg_clause_size; j++)
                    {
                        uint64_t neg_clause_idx = neg_clauses[j];
                        clause new_clause;
                        uint64_t pos_lit_size = _clauses[pos_clause_idx].literals.size();
                        uint64_t neg_lit_size = _clauses[neg_clause_idx].literals.size();
                        new_clause.literals.reserve(pos_lit_size + neg_lit_size);
                        bool is_tautology = false;
                        for (int k = 0; k < pos_lit_size; k++)
                        {
                            int l_sign_idx = _clauses[pos_clause_idx].literals[k];
                            if (_lits[std::abs(l_sign_idx)].is_nia_lit || _lits[std::abs(l_sign_idx)].delta != bool_var_idx)
                            {
                                new_clause.literals.push_back(l_sign_idx);
                            }
                        } // add the lits in pos clause to new clause
                        for (int k = 0; k < neg_lit_size; k++)
                        {
                            int l_sign_idx = _clauses[neg_clause_idx].literals[k];
                            if (_lits[std::abs(l_sign_idx)].is_nia_lit || _lits[std::abs(l_sign_idx)].delta != bool_var_idx)
                            {
                                bool is_existed_lit = false;
                                for (uint64_t i = 0; i < pos_lit_size - 1; i++)
                                {
                                    if (l_sign_idx == (new_clause.literals[i]))
                                    {
                                        is_existed_lit = true;
                                        break;
                                    } // if the lit has existed, then it will not be added
                                    if (l_sign_idx == (-new_clause.literals[i]))
                                    {
                                        is_tautology = true;
                                        break;
                                    } // if there exists (aVb)^(-aV-b), the new clause is tautology
                                }
                                if (is_tautology)
                                {
                                    break;
                                }
                                if (!is_existed_lit)
                                {
                                    new_clause.literals.push_back(l_sign_idx);
                                }
                            }
                        }
                        if (!is_tautology)
                        {
                            __int128_t clause_lit_hash = hash_lits_to_num(new_clause.literals);
                            bool should_add = false;
                            if (clauselit_map.find(clause_lit_hash) == clauselit_map.end())
                            {
                                should_add = true;
                            } // the clause never appears
                            else
                            {
                                int origin_clause_idx = clauselit_map[clause_lit_hash];
                                clause *cl_origin = &(_clauses[origin_clause_idx]);
                                if (cl_origin->is_delete)
                                {
                                    should_add = true;
                                } // the clause has been deleted
                                else if (!is_same_lits(cl_origin->literals, new_clause.literals))
                                {
                                    should_add = true;
                                } // not the same one
                            }
                            if (should_add)
                            { // add new clause, if it never appers then add it
                                for (int l_sign_idx : new_clause.literals)
                                {
                                    lit *l_inner = &(_lits[std::abs(l_sign_idx)]);
                                    if (!l_inner->is_nia_lit)
                                    {
                                        _resolution_vars[l_inner->delta].clause_idxs.push_back((int)_num_clauses);
                                    }
                                }
                                _clauses.push_back(new_clause);
                                clauselit.push_back(clause_lit_hash);
                                clauselit_map[clause_lit_hash] = (int)_num_clauses;
                                _num_clauses++;
                            }
                        }
                    }
                }
                for (int i = 0; i < pos_clause_size; i++)
                {
                    clause pos_cl = _clauses[pos_clauses[i]];
                    for (int j = 0; j < pos_cl.literals.size(); j++)
                    {
                        int l_idx = pos_cl.literals[j];
                        lit *l = &(_lits[std::abs(l_idx)]);
                        if (!l->is_nia_lit && l->delta == bool_var_idx)
                        {
                            pos_cl.literals[j] = pos_cl.literals[0];
                            pos_cl.literals[0] = l_idx;
                            break;
                        }
                    }
                    _reconstruct_stack.push(pos_cl);
                }
                for (int i = 0; i < neg_clause_size; i++)
                {
                    clause neg_cl = _clauses[neg_clauses[i]];
                    for (int j = 0; j < neg_cl.literals.size(); j++)
                    {
                        int l_idx = neg_cl.literals[j];
                        lit *l = &(_lits[std::abs(l_idx)]);
                        if (!l->is_nia_lit && l->delta == bool_var_idx)
                        {
                            neg_cl.literals[j] = neg_cl.literals[0];
                            neg_cl.literals[0] = l_idx;
                            break;
                        }
                    }
                    _reconstruct_stack.push(neg_cl);
                }
            }
        }
    }
    bool cmp_vlt_by_var(var_lit_term vlt1, var_lit_term vlt2) { return vlt1.var_idx < vlt2.var_idx || (vlt1.var_idx == vlt2.var_idx && vlt1.term_idx < vlt2.term_idx); }
    bool cmp_vlt_by_lit(var_lit_term vlt1, var_lit_term vlt2) { return vlt1.lit_idx < vlt2.lit_idx || (vlt1.lit_idx == vlt2.lit_idx && vlt1.term_idx < vlt2.term_idx); }
    void ls_solver::reduce_clause()
    {
        // std::cout<<_num_clauses<<std::endl;
        bool_var_vec.clear();
        nia_var_vec.clear();
        _vars.reserve(_resolution_vars.size());
        int i, reduced_clause_num;
        i = 0;
        reduced_clause_num = 0;
        for (; i < _num_clauses; i++)
        {
            if (!_clauses[i].is_delete)
            {
                _clauses[reduced_clause_num++] = _clauses[i];
            }
        }
        _clauses.resize(reduced_clause_num);

        _num_nia_lits = 0;
        _num_bool_lits = 0;
        for (int l_idx = 0; l_idx < _lits.size(); l_idx++)
        {
            _lits[l_idx].lits_index = 0;
        } // reset the lit_index
        // transfer the resolution vars to vars
        _num_clauses = reduced_clause_num;
        lit_appear.resize(_num_lits + _additional_len, false);
        term_appear.resize(_terms.size() + _additional_len, false);
        for (int clause_idx = 0; clause_idx < reduced_clause_num; clause_idx++)
        {
            _clauses[clause_idx].weight = 1;
            for (int k = 0; k < _clauses[clause_idx].literals.size(); k++)
            {
                int l_sign_idx = _clauses[clause_idx].literals[k];
                lit *l = &(_lits[std::abs(l_sign_idx)]);
                if (l->is_nia_lit)
                {
                    variable *v;
                    for (int j = 0; j < l->coff_terms.size(); j++)
                    {
                        term *t = &(_terms[l->coff_terms[j].term_idx]);
                        if (!term_appear[l->coff_terms[j].term_idx])
                        {
                            for (var_exp &ve : t->var_epxs)
                            {
                                ve.var_index = (int)transfer_name_to_reduced_var(_resolution_vars[ve.var_index].var_name, true);
                            }
                            term_appear[l->coff_terms[j].term_idx] = true;
                        }
                        for (var_exp &ve : t->var_epxs)
                        {
                            v = &(_vars[ve.var_index]);
                            v->clause_idxs.push_back(clause_idx);
                        }
                    }
                    _clauses[clause_idx].nia_literals.push_back(l_sign_idx);
                }
                else
                {
                    if (!lit_appear[std::abs(l_sign_idx)])
                    {
                        l->delta = transfer_name_to_reduced_var(_resolution_vars[l->delta].var_name, false);
                        _vars[l->delta].literal_idxs.push_back(std::abs(l_sign_idx)); // for a boolean var, its first lit_idx is the lit containing the var
                    }
                    _vars[l->delta].clause_idxs.push_back(clause_idx);
                    _vars[l->delta].bool_var_in_pos_clause.push_back(l_sign_idx > 0); // for a boolean var, if it is neg in a clause, it is false
                    _clauses[clause_idx].bool_literals.push_back(l_sign_idx);
                }
                if (!lit_appear[std::abs(l_sign_idx)])
                {
                    lit_appear[std::abs(l_sign_idx)] = true;
                    _lits[std::abs(l_sign_idx)].lits_index = std::abs(l_sign_idx);
                }
            }
        }
        //soft 
        for(int i=0;i<_soft_clauses.size();i++)
        {
            //weight init TODO
            _soft_clauses[i].weight=_soft_clauses[i].org_weight;
            for (int k = 0; k < _soft_clauses[i].literals.size(); k++)
            {
                int l_sign_idx = _soft_clauses[i].literals[k];
                lit *l = &(_lits[std::abs(l_sign_idx)]);
                if (l->is_nia_lit)
                {
                    variable *v;
                    for (int j = 0; j < l->coff_terms.size(); j++)
                    {
                        term *t = &(_terms[l->coff_terms[j].term_idx]);
                        if (!term_appear[l->coff_terms[j].term_idx])
                        {
                            for (var_exp &ve : t->var_epxs)
                            {
                                ve.var_index = (int)transfer_name_to_reduced_var(_resolution_vars[ve.var_index].var_name, true);
                            }
                            term_appear[l->coff_terms[j].term_idx] = true;
                        }
                        for (var_exp &ve : t->var_epxs)
                        {
                            v = &(_vars[ve.var_index]);
                            v->soft_clause_idxs.push_back(i);
                        }
                    }
                    _soft_clauses[i].nia_literals.push_back(l_sign_idx);
                }
                else
                {
                    std::cout<<"soft error with bool"<<std::endl;
                    //Todo::
                    // if (!lit_appear[std::abs(l_sign_idx)])
                    // {
                    //     l->delta = transfer_name_to_reduced_var(_resolution_vars[l->delta].var_name, false);
                    //     _vars[l->delta].literal_idxs.push_back(std::abs(l_sign_idx)); // for a boolean var, its first lit_idx is the lit containing the var
                    // }
                    // _vars[l->delta].clause_idxs.push_back(i);
                    // _vars[l->delta].bool_var_in_pos_clause.push_back(l_sign_idx > 0); // for a boolean var, if it is neg in a clause, it is false
                    // _clauses[i].bool_literals.push_back(l_sign_idx);
                }
                if (!lit_appear[std::abs(l_sign_idx)])
                {
                    lit_appear[std::abs(l_sign_idx)] = true;
                    _lits[std::abs(l_sign_idx)].lits_index = std::abs(l_sign_idx);
                }
            }
        }
        // exit(0);

        //soft


        _vars.resize(_vars.size());
        _num_vars = _vars.size();
        _num_nia_vars = 0;
        for (variable &v : _vars)
        {
            uint64_t pre_clause_idx = INT64_MAX;
            int var_clause_num = 0;
            int var_soft_clause_num = 0;
            for (int i = 0; i < v.clause_idxs.size(); i++)
            {
                uint64_t tmp_clause_idx = v.clause_idxs[i];
                if (pre_clause_idx != tmp_clause_idx)
                {
                    pre_clause_idx = tmp_clause_idx;
                    v.clause_idxs[var_clause_num++] = (int)pre_clause_idx;
                }
            }
            pre_clause_idx = INT64_MAX;
            for (int i = 0; i < v.soft_clause_idxs.size(); i++)
            {
                uint64_t tmp_clause_idx = v.soft_clause_idxs[i];
                if (pre_clause_idx != tmp_clause_idx)
                {
                    pre_clause_idx = tmp_clause_idx;
                    v.soft_clause_idxs[var_soft_clause_num++] = (int)pre_clause_idx;
                }
            }
            v.clause_idxs.resize(var_clause_num);
            v.soft_clause_idxs.resize(var_soft_clause_num);
            if (v.is_nia)
            {
                v.upper_bound = _resolution_vars[transfer_name_to_resolution_var(v.var_name, true)].upper_bound;
                v.low_bound = _resolution_vars[transfer_name_to_resolution_var(v.var_name, true)].low_bound;
                _num_nia_vars++;
            }
        } // determine the clause_idxs of var
        lit *l;
        term *t;
        for (int l_idx = 0; l_idx < _lits.size(); l_idx++)
        {
            l = &(_lits[l_idx]);
            if (l->lits_index == 0)
            {
                continue;
            }
            for (int pos_term_idx = 0; pos_term_idx < l->coff_terms.size(); pos_term_idx++)
            {
                uint64_t term_idx = l->coff_terms[pos_term_idx].term_idx;
                int coff = l->coff_terms[pos_term_idx].coff;
                t = &(_terms[term_idx]);
                for (int ve_idx = 0; ve_idx < t->var_epxs.size(); ve_idx++)
                {
                    uint64_t var_idx = t->var_epxs[ve_idx].var_index;
                    var_lit_term vlt(var_idx, term_idx, l_idx, coff);
                    _vars[var_idx].var_lit_terms.push_back(vlt);
                    l->var_lit_terms.push_back(vlt);
                }
            }
        } // determine the var_lit_term of var and lit, the vlt has been sorted by the lit_idx in vars
        for (lit &l : _lits)
        {
            if (l.lits_index != 0)
            {
                std::sort(l.var_lit_terms.begin(), l.var_lit_terms.end(), cmp_vlt_by_var);
            }
        } // sort the vlt in lit by its var_idx
        for (variable &v : _vars)
        {
            uint64_t pre_lit_idx = INT64_MAX;
            int var_lit_num = 0;
            int var_soft_lit_num =0;
            for (int i = 0; i < v.var_lit_terms.size(); i++)
            {
                uint64_t tmp_lit_idx = v.var_lit_terms[i].lit_idx;
                if (pre_lit_idx != tmp_lit_idx)
                {
                    // var_lit_num++;
                    pre_lit_idx = tmp_lit_idx;
                    if(_lits[pre_lit_idx].is_soft==0) {v.literal_idxs.push_back(pre_lit_idx);var_lit_num++;}
                    else {v.soft_literal_idxs.push_back(pre_lit_idx);var_soft_lit_num++;}
                }
            }
            v.literal_idxs.resize(var_lit_num);
            v.soft_literal_idxs.resize(var_soft_lit_num);
        } // determine the lit_idxs of var
        var_in_long_term = new Array((int)_num_vars + (int)_additional_len);
        for (uint64_t term_idx = 0; term_idx < _terms.size(); term_idx++)
        {
            if (!term_appear[term_idx])
            {
                continue;
            }
            t = &(_terms[term_idx]);
            std::sort(t->var_epxs.begin(), t->var_epxs.end(), cmp_ve);
            int curr_var_idx = -1;
            for (var_exp &ve : t->var_epxs)
            {
                _vars[ve.var_index].term_idxs.push_back(term_idx);
                if (curr_var_idx == ve.var_index)
                {
                    has_high_coff = true;
                    return;
                }
                else
                {
                    curr_var_idx = ve.var_index;
                }
            }
            if (t->var_epxs.size() > 2)
            {
                for (var_exp &ve : t->var_epxs)
                {
                    var_in_long_term->insert_element(ve.var_index);
                }
            }
        } // determine the term_idxs of vars
        // print_formula_with_soft();
        // exit(0);
    }

    void ls_solver::make_space()
    {
        _solution.resize(_num_vars + _additional_len);
        _best_solutin.resize(_num_vars + _additional_len);
        tabulist.resize(2 * _num_vars + _additional_len, 0);
        operation_var_idx_vec.resize(_num_opt + _additional_len);
        operation_var_idx_bool_vec.resize(_num_opt + _additional_len);
        operation_change_value_vec.resize(_num_opt + _additional_len);
        last_move.resize(2 * _num_vars + _additional_len, 0);
        unsat_clauses = new Array((int)_num_clauses + (int)_additional_len);
        sat_clause_with_false_literal = new Array((int)_num_clauses + (int)_additional_len);
        false_lit_occur = new Array((int)_num_lits + (int)_additional_len);
        contain_bool_unsat_clauses = new Array((int)_num_clauses);
        is_chosen_bool_var.resize(_num_vars + _additional_len, false);
        _lit_make_break.resize(_num_lits + _additional_len, 0);
        term_coffs.resize(_terms.size() + _additional_len, 0);
        //soft new
        unsat_soft_clauses = new Array((int)_num_soft_clauses + (int)_additional_len);
        contain_bool_unsat_soft_clauses = new Array((int)_num_soft_clauses);
        sat_soft_clause_with_false_literal = new Array((int)_num_soft_clauses + (int)_additional_len);
    }

    void ls_solver::set_pre_value()
    {
        _pre_value_1.resize(_num_vars + _additional_len, INT32_MAX);
        _pre_value_2.resize(_num_vars + _additional_len, INT32_MAX);
        for (clause &cl : _clauses)
        {
            if (cl.literals.size() == 1 && cl.literals[0] > 0 && _lits[cl.literals[0]].is_equal)
            {
                lit *l = &(_lits[cl.literals[0]]);
                if (l->coff_terms.size() == 1 && _terms[l->coff_terms[0].term_idx].var_epxs.size() == 1)
                {
                    int var_idx = _terms[l->coff_terms[0].term_idx].var_epxs[0].var_index;
                    _pre_value_1[var_idx] = (int)(-l->key / l->coff_terms[0].coff);
                }
            } //(a==0)
            else if (cl.literals.size() == 2 && cl.literals[0] > 0 && _lits[cl.literals[0]].is_equal && cl.literals[1] > 0 && _lits[cl.literals[1]].is_equal)
            {
                lit *l1 = &(_lits[cl.literals[0]]);
                lit *l2 = &(_lits[cl.literals[1]]);
                if ((l1->coff_terms.size() == 1) && (l2->coff_terms.size() == 1))
                {
                    term *t_1 = &(_terms[l1->coff_terms[0].term_idx]);
                    term *t_2 = &(_terms[l2->coff_terms[0].term_idx]);
                    if (t_1->var_epxs.size() == 1 && t_2->var_epxs.size() == 1 && t_1->var_epxs[0].var_index == t_2->var_epxs[0].var_index)
                    {
                        int var_idx = t_1->var_epxs[0].var_index;
                        _pre_value_1[var_idx] = (int)(-l1->key / l1->coff_terms[0].coff);
                        _pre_value_2[var_idx] = (int)(-l2->key / l2->coff_terms[0].coff);
                    }
                }
            } //(a==0 OR a==1)
        }
    }
}
