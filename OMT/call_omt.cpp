//
//  call.cpp
//  lia_ls
//
//  Created by XiangHe on 2024/5/4.
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
    fclose(stdin);
    cin.clear();
    freopen(argv[2], "r", stdin);
    getline(cin, in_string);
    // m_ls->get_objective(in_string);
    fclose(stdin);
    m_ls->build_instance(vec);
    m_ls->get_objective(in_string);
    m_ls->local_search();
    // std::cout<<vec.size()<<std::endl;
    return 0;
}
}
using namespace call;
int main(int argc,char *argv[]){
    Call_fun c;
    c.func(argc,argv);
    return 0;
}
