//
//  call.cpp
//  lia_ls
//
//  Created by DouglasLee on 2021/11/2.
//

#include "call.hpp"
using namespace std;
namespace call{
Call_fun::Call_fun(){
    m_ls=new nia::ls_solver(0);
    m_ls_sub=new nia::ls_solver(0);
}

int Call_fun::func(int argc,char *argv[]){
    string in_string;
    uint64_t num_lits;// long long int
    freopen(argv[1],"r",stdin);
    cin>>num_lits;
    m_ls->make_lits_space(num_lits);//此处需要设定lits数量
    getline(cin,in_string);
    getline(cin, in_string);
    std::vector<std::string> lits_copy;
    while(in_string!="0"){
        lits_copy.push_back(in_string);
        m_ls->build_lits(in_string);//传入string到lits
        getline(cin,in_string);
    }
    // getline(cin,in_string);
    // getline(cin,in_string);
    int size;
    cin>>size;
    std::vector<std::vector<int>> vec;
    vec.resize(size);
    int size_now=0;
    while(size_now<size){
        cin>>in_string;
        if(in_string=="(")continue;
        else if(in_string==")"){size_now++;}
        else{vec[size_now].push_back(atoi(in_string.c_str()));}
    }
    // std::cout<<vec.size()<<std::endl;
    fclose(stdin);
    cin.clear();
    std::vector<std::vector<int>> new_hard_clauses;
    std::vector<std::vector<int>> not_used;
    // m_ls->build_soft_lits(argv[2]);
    bool is_or_hard=m_ls->build_new_hard_lits(argv[2],new_hard_clauses,true);//通过这个函数返回一个是不是有or的,并且得到pseudo_hard_clause_weight
    int obj_1,obj_2,obj_final;//设置两个m_ls,有的话一人一半时间跑
    if(is_or_hard)
    {
        //m_ls_sub start
        m_ls_sub->make_lits_space(num_lits);
        for(auto lit_copy:lits_copy)
        {
            m_ls_sub->build_lits(lit_copy);
        }
        // m_ls_sub->build_soft_lits(argv[2]);
        m_ls_sub->build_new_hard_lits(argv[2],not_used,false);
        m_ls_sub->build_instance(vec);
        obj_1=m_ls_sub->local_search(is_or_hard);
        //m_ls start with new hard lits;
        for(auto new_hard_clause:new_hard_clauses)
        {
            vec.push_back(new_hard_clause);
        }
        m_ls->build_instance(vec);
        obj_2=m_ls->local_search(is_or_hard);
        if(obj_1==-1&&obj_2==-1)  obj_final=-1;
        else if(obj_1==-1)  obj_final=obj_2;
        else if(obj_2==-1)  obj_final=obj_1+m_ls->get_pseudo_hard_clause_weight();
        else  obj_final=min(obj_1+m_ls->get_pseudo_hard_clause_weight(),obj_2);
    }
    else 
    {
        m_ls->build_instance(vec);
        obj_final=m_ls->local_search(is_or_hard);
    }
    std::cout<<obj_final;
    return 0;
}
}
using namespace call;
int main(int argc,char *argv[]){
    Call_fun c;
    c.func(argc,argv);
    return 0;
}
