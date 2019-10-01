#ifndef BFSSEARCHING_H_INCLUDED
#define BFSSEARCHING_H_INCLUDED
#include"_Matrix.h"
#include <iostream>
using namespace std;

//���׶η� ��������B, N, CB, CN, b,BV�±����BV,NBV,�˹�
//�ص��飬�����������Ҫ��ַ���룬�����¾���ʱӦ������

bool is_nofeasiblesolution(_Matrix BV,_Matrix initialBV)//initialBV�ǵ�һ�׶γ�ʼʱ���˹�����
{
    for(int i=0;i<=(initialBV.n-1);i++)
    {
        for(int k=0;k<=BV.n-1;k++)
        {
            if(initialBV.read(0,i)==BV.read(0,k))
                return true;
        }//ֻҪ����BV���������ʼ���˹���������Ϊnofeasiblesolution
    }
    return false;
}
bool is_infinite(_Matrix RN)//��������Ž������Ϊĳ�ǻ�����������Ϊ0
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
bool is_nomorethan0(_Matrix RN)//Ĭ�ϸ���1*n�ľ���
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
    _Matrix_Calc g; //gΪ��ʽ������Ϊ���ܹ����ü��㺯��
    _Matrix RN(1,N.n),temp1(B.m,N.n),temp2(1,N.n),cnt(CN.n,CN.m),cbt(CB.n,CB.m),b_1(B.m,B.n);
    g.transpos(&CN,&cnt);
    g.transpos(&CB,&cbt);
    g.inverse(&B,&b_1);
    g.multiply(&b_1,&N,&temp1);  //temp1=b_1*N
    g.multiply(&cbt,&temp1,&temp2);  //temp2=cbt*b_1*n
    g.subtract(&cnt,&temp2,&RN);
    return RN;
}

int find_entering(_Matrix RN,_Matrix NBV,float &nameofentering)//�ҵ�����������±������������ֵΪ����j��0�п�ʼ����
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
_Matrix get_blandrules(_Matrix B,_Matrix b,_Matrix N,int j)//jΪentering var����
{
    //blandrules=(b_1*b)/(b_1*Nxj)
    _Matrix_Calc g;
    _Matrix b_1(B.m,B.n),blandrules(1,B.m),temp1(B.m,1),temp2(N.m,1),temp3(B.m,1);
    g.inverse(&B,&b_1);
    g.multiply(&b_1,&b,&temp1);//temp1�Ƿ���=B_1*b
    for(int i=0;i<=(N.m-1);i++)
    {
        temp2.write(i,0,N.read(i,j));//temp2��ȡNxj
    }
    g.multiply(&b_1,&temp2,&temp3);//temp3Ϊ��ĸ
    for(int k=0;k<=(B.m-1);k++)
    {
        blandrules.write(0,k,(temp1.read(k,0))/(temp3.read(k,0)));
    }
    return blandrules;
}
int find_leaving(_Matrix blandrules,_Matrix BV,float &nameofleaving)//�ҵ��뿪�������±������������ֵΪ����p��0�п�ʼ��
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
                        i=k-1;//��=k-1��������ѭ����ʼ��һ����ѭ����k��ʼ
                        flag=true;
                        break;
                    }
                }
            }
            if(!flag)
                break;
        flag=false;
        }
    }//�ҵ���i��Ϊ��С����
    nameofleaving=BV.read(0,p);
    return p;
}
void changebvnbv(_Matrix &BV,_Matrix &NBV,int j,int p,float nameofentering,float nameofleaving)//j->entering,p->leaving
{
    float temp1,temp2;
    temp1=BV.read(0,p);
    temp2=NBV.read(0,j);//temp1Ϊleaving���±꣬temp2Ϊentering���±�
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
    }//����B,V
    temp2=CN.read(j,0);
    CN.write(j,0,CB.read(p,0));
    CB.write(p,0,temp2);//����CB��CN
}
//�ڶ��׶Σ�bv��b��cb���䣬��Ҫ����nbv��n��cn
_Matrix changesecondphaseNBV(_Matrix NBV,_Matrix BV,_Matrix originalBV)//originalBVΪ�˹������������ʼʱBV���±����
{
    _Matrix secondphaseNBV(1,(NBV.n-BV.n));//�µ�NBV��������ԭ��NBV������ȥBV������Ϊ�˹���������ΪBV��
    bool flag=false;
    int counter=-1;
    for(int i=0;i<=NBV.n-1;i++)//iѭ����NBV��
    {
        for(int k=0;k<=originalBV.n-1;k++)//kѭ����originalBV��
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
    for(int i=0;i<=NBV.n-1;i++)//iѭ����NBV��
    {
        for(int k=0;k<=originalBV.n-1;k++)//kѭ����originalBV��
        {
            if(NBV.read(0,i)==originalBV.read(0,k))//���NBV������������˹�����
            {
                flag=true;
                break;
            }
        }
        if(!flag)
        {
            counter+=1;//couter��Ӧ�µ�NBV�ĵ�ĳ��
            secondphaseCN.write(counter,0,originalC.read(NBV.read(0,i)-1,0));//��ΪoriginalC�ǰ���123567˳������
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
//changeseondphaseϵ�����������Ĳ�����NBV��Ϊ�����˹�������NBV
_Matrix changesecondphaseN(_Matrix NBV,_Matrix BV,_Matrix originalBV,_Matrix N)
{
    _Matrix secondphaseN(N.m,(NBV.n-BV.n));
    bool flag=false;
    int counter=-1;
    for(int i=0;i<=NBV.n-1;i++)//iѭ����NBV��
    {
        for(int k=0;k<=originalBV.n-1;k++)//kѭ����originalBV��
        {
            if(NBV.read(0,i)==originalBV.read(0,k))
            {
                flag=true;
                break;
            }
        }
        if(!flag)
        {
            counter+=1;//counter��Ӧ�µ�NBV�ĵ�ĳ��
            for(int k1=0;k1<=N.m-1;k1++)
            {
                secondphaseN.write(k1,counter,N.read(k1,i));
            }
        }
        flag=false;
    }
    return secondphaseN;
}
//x=B_1*b,bΪ�о���B.m*1��,opt=cbt*x
void printopt(_Matrix NBV,_Matrix BV,_Matrix b,_Matrix B,_Matrix CB)
{
    _Matrix b_1(B.m,B.n),temp1(B.m,1),temp2(1,1),cbt(1,B.m);
    _Matrix_Calc g;
    g.inverse(&B,&b_1);
    g.multiply(&b_1,&b,&temp1);//temp1���������xֵ=B_1*b
    for(int i=0;i<=NBV.n-1;i++)
    {
        std::cout<<"x"<<NBV.read(0,i)<<"=0"<<endl;//����ǻ�����Ϊ0
    }
    for(int i=0;i<=BV.n-1;i++)
    {
        std::cout<<"x"<<BV.read(0,i)<<"="<<temp1.read(i,0)<<endl;//���������ֵ
    }
    g.transpos(&CB,&cbt);
    g.multiply(&cbt,&temp1,&temp2);
    std::cout<<"opt="<<temp2.read(0,0)<<endl;
    cout<<"thank you for using, have a nice day!"<<endl;
}
#endif // BFSSEARCHING_H_INCLUDED
