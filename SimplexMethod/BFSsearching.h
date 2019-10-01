#ifndef BFSSEARCHING_H_INCLUDED
#define BFSSEARCHING_H_INCLUDED
#include"_Matrix.h"
#include <iostream>
using namespace std;

//两阶段法 给出矩阵B, N, CB, CN, b,BV下标矩阵BV,NBV,人工
//重点检查，矩阵的运算需要地址传入，构造新矩阵时应该声明

bool is_nofeasiblesolution(_Matrix BV,_Matrix initialBV)//initialBV是第一阶段初始时的人工变量
{
    for(int i=0;i<=(initialBV.n-1);i++)
    {
        for(int k=0;k<=BV.n-1;k++)
        {
            if(initialBV.read(0,i)==BV.read(0,k))
                return true;
        }//只要最后的BV中留有最初始的人工变量，即为nofeasiblesolution
    }
    return false;
}
bool is_infinite(_Matrix RN)//无穷多最优解的条件为某非基变量检验数为0
{
    for(int i=0;i<=RN.n-1;i++)
    {
        if(RN.read(0,i)==0)
            return true;
    }
    return false;
}
bool is_unbounded(_Matrix blandrules)
{
    for(int i=0;i<=blandrules.n-1;i++)
    {
        if(blandrules.read(0,i)>0)
            return false;
    }
    return true;
}
bool is_nomorethan0(_Matrix RN)//默认给出1*n的矩阵
{
    bool flag=true;
    for(int i=0;i<=(RN.n-1);i++)
    {
        if(RN.read(0,i)>0)
        {
            flag=false;
            break;
        }
    }
    return flag;
}
_Matrix get_chekingnumber(_Matrix CN,_Matrix CB,_Matrix B,_Matrix N )
{
   //RN=cnt-cbt*b_1*n
    _Matrix_Calc g; //g为形式变量，为了能够调用计算函数
    _Matrix RN(1,N.n),temp1(B.m,N.n),temp2(1,N.n),cnt(CN.n,CN.m),cbt(CB.n,CB.m),b_1(B.m,B.n);
    g.transpos(&CN,&cnt);
    g.transpos(&CB,&cbt);
    g.inverse(&B,&b_1);
    g.multiply(&b_1,&N,&temp1);  //temp1=b_1*N
    g.multiply(&cbt,&temp1,&temp2);  //temp2=cbt*b_1*n
    g.subtract(&cnt,&temp2,&RN);
    return RN;
}

int find_entering(_Matrix RN,_Matrix NBV,float &nameofentering)//找到进入变量的下标和列数，返回值为列数j（0行开始），
{
    int j=-1;
    for(int i=0;i<=(RN.n-1);i++)
    {
        if(RN.read(0,i)>0)
            {
                j=i;
                break;
            }
    }
    nameofentering=NBV.read(0,j);
    return j;
}
_Matrix get_blandrules(_Matrix B,_Matrix b,_Matrix N,int j)//j为entering var的行
{
    //blandrules=(b_1*b)/(b_1*Nxj)
    _Matrix_Calc g;
    _Matrix b_1(B.m,B.n),blandrules(1,B.m),temp1(B.m,1),temp2(N.m,1),temp3(B.m,1);
    g.inverse(&B,&b_1);
    g.multiply(&b_1,&b,&temp1);//temp1是分子=B_1*b
    for(int i=0;i<=(N.m-1);i++)
    {
        temp2.write(i,0,N.read(i,j));//temp2读取Nxj
    }
    g.multiply(&b_1,&temp2,&temp3);//temp3为分母
    for(int k=0;k<=(B.m-1);k++)
    {
        blandrules.write(0,k,(temp1.read(k,0))/(temp3.read(k,0)));
    }
    return blandrules;
}
int find_leaving(_Matrix blandrules,_Matrix BV,float &nameofleaving)//找到离开变量的下标和列数，返回值为列数p（0行开始）
{
    bool flag=false;
    int p;
    for(int i=0;i<=(blandrules.n-1);i++)
    {
        if(blandrules.read(0,i)>0)
        {
            p=i;
            for(int k=i+1;k<=(blandrules.n-1);k++)
            {
                if(blandrules.read(0,k)>0)
                {
                    if(blandrules.read(0,k)<blandrules.read(0,i))
                    {
                        i=k-1;//让=k-1这样跳出循环后开始下一个大循环从k开始
                        flag=true;
                        break;
                    }
                }
            }
            if(!flag)
                break;
        flag=false;
        }
    }//找到第i行为最小正数
    nameofleaving=BV.read(0,p);
    return p;
}
void changebvnbv(_Matrix &BV,_Matrix &NBV,int j,int p,float nameofentering,float nameofleaving)//j->entering,p->leaving
{
    float temp1,temp2;
    temp1=BV.read(0,p);
    temp2=NBV.read(0,j);//temp1为leaving的下标，temp2为entering的下标
    NBV.write(0,j,temp1);
    BV.write(0,p,temp2);
}
void changebncbcn(_Matrix &B,_Matrix &N,_Matrix &CB,_Matrix &CN,int j,int p)//j->entering,p->leaving
{
    _Matrix temp1(B.m,1);
    float temp2;
    for(int i=0;i<=(B.m-1);i++)
    {
        temp1.write(i,0,N.read(i,j));
        N.write(i,j,B.read(i,p));
        B.write(i,p,temp1.read(i,0));
    }//更改B,V
    temp2=CN.read(j,0);
    CN.write(j,0,CB.read(p,0));
    CB.write(p,0,temp2);//更改CB，CN
}
//第二阶段，bv和b，cb不变，需要更改nbv，n，cn
_Matrix changesecondphaseNBV(_Matrix NBV,_Matrix BV,_Matrix originalBV)//originalBV为人工变量即最最初始时BV的下标矩阵
{
    _Matrix secondphaseNBV(1,(NBV.n-BV.n));//新的NBV列数等于原来NBV列数减去BV数，因为人工变量数即为BV数
    bool flag=false;
    int counter=-1;
    for(int i=0;i<=NBV.n-1;i++)//i循环在NBV里
    {
        for(int k=0;k<=originalBV.n-1;k++)//k循环在originalBV里
        {
            if(NBV.read(0,i)==originalBV.read(0,k))
            {
                flag=true;
                break;
            }
        }
        if(!flag)
        {
            counter+=1;
            secondphaseNBV.write(0,counter,NBV.read(0,i));
        }
        flag=false;
    }
    return secondphaseNBV;
}
_Matrix changesecondphaseCN(_Matrix NBV,_Matrix BV,_Matrix originalBV,_Matrix originalC)
{
    _Matrix secondphaseCN((NBV.n-BV.n),1);
    bool flag=false;
    int counter=-1;
    for(int i=0;i<=NBV.n-1;i++)//i循环在NBV里
    {
        for(int k=0;k<=originalBV.n-1;k++)//k循环在originalBV里
        {
            if(NBV.read(0,i)==originalBV.read(0,k))//如果NBV中这个变量是人工变量
            {
                flag=true;
                break;
            }
        }
        if(!flag)
        {
            counter+=1;//couter对应新的NBV的第某列
            secondphaseCN.write(counter,0,originalC.read(NBV.read(0,i)-1,0));//认为originalC是按照123567顺序排列
        }
        flag=false;
    }
    return secondphaseCN;
}
_Matrix changesecondphaseCB(_Matrix BV,_Matrix originalC)
{
    _Matrix secondphaseCB(BV.n,1);
    for(int i=0;i<=BV.n-1;i++)
    {
        secondphaseCB.write(i,0,originalC.read(BV.read(0,i)-1,0));
    }
    return secondphaseCB;
}
//changeseondphase系列三个函数的参数中NBV均为含有人工变量的NBV
_Matrix changesecondphaseN(_Matrix NBV,_Matrix BV,_Matrix originalBV,_Matrix N)
{
    _Matrix secondphaseN(N.m,(NBV.n-BV.n));
    bool flag=false;
    int counter=-1;
    for(int i=0;i<=NBV.n-1;i++)//i循环在NBV里
    {
        for(int k=0;k<=originalBV.n-1;k++)//k循环在originalBV里
        {
            if(NBV.read(0,i)==originalBV.read(0,k))
            {
                flag=true;
                break;
            }
        }
        if(!flag)
        {
            counter+=1;//counter对应新的NBV的第某列
            for(int k1=0;k1<=N.m-1;k1++)
            {
                secondphaseN.write(k1,counter,N.read(k1,i));
            }
        }
        flag=false;
    }
    return secondphaseN;
}
//x=B_1*b,b为列矩阵（B.m*1）,opt=cbt*x
void printopt(_Matrix NBV,_Matrix BV,_Matrix b,_Matrix B,_Matrix CB)
{
    _Matrix b_1(B.m,B.n),temp1(B.m,1),temp2(1,1),cbt(1,B.m);
    _Matrix_Calc g;
    g.inverse(&B,&b_1);
    g.multiply(&b_1,&b,&temp1);//temp1储存基变量x值=B_1*b
    for(int i=0;i<=NBV.n-1;i++)
    {
        std::cout<<"x"<<NBV.read(0,i)<<"=0"<<endl;//输出非基变量为0
    }
    for(int i=0;i<=BV.n-1;i++)
    {
        std::cout<<"x"<<BV.read(0,i)<<"="<<temp1.read(i,0)<<endl;//输出基变量值
    }
    g.transpos(&CB,&cbt);
    g.multiply(&cbt,&temp1,&temp2);
    std::cout<<"opt="<<temp2.read(0,0)<<endl;
    cout<<"thank you for using, have a nice day!"<<endl;
}
#endif // BFSSEARCHING_H_INCLUDED
