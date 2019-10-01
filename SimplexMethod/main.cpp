#include <stdio.h>
#include <iostream>
#include "_Matrix.h"
#include"BFSsearching.h"

//���ٶȱ����������˲�
using namespace std;

//��ӡ2ά����


int main()
{
    //����ԭʼLP
    int type;
    cout<<"������max��1��������min��-1����";
    cin>>type;//���ڰ�min���max
    int m,n;
    cout<<"������constrain��Ŀ���ܱ�����Ŀ��";
    cin>>m;cin>>n;
    _Matrix ori(m,n),oriC(1,n),b(m,1);
    int *p=new int[m];
    cout<<"�밴˳������obj�б�����ϵ��(�ո�ֿ�������������������ֵ����б��������obj�в����֣���0����)��";

    int j;
    for(int i=0;i<n;++i){
        cin>>j;
        oriC.write(0,i,type*j);
    }

    int c;
    int num=1;
    for(int i=0;i<m;++i){
        cout<<"�������"<<i<<"����������(����ֻ��ϵ������,��)";
        for(int j=0;j<n;++j){
            cin>>c;
            ori.write(i,j,c);
        }
    }
    cout<<"������ÿһ������������b��";
    for(int i=0;i<m;++i){
        cin>>c;
        b.write(i,0,c);
    }
    cout<<"������ÿһ������������>(-1)=(0)<(1):";
    for(int i=0;i<m;++i){
        cin>>c;
        p[i]=c;
    }


    //���׼��ʽ
    //����p[]�������Ϣȷ�������ӵı�������
    num=0;
    for(int i=0;i<m;++i){
        if(p[i]!=0) ++num;
    }
    num+=n;//StandardForm����ı�������


    _Matrix Standard(m,num),StandardC(1,num);

    //����ori���������
    for(int i=0;i<m;++i){
        for(int j=0;j<n;++j){
            Standard.write(i,j,ori.read(i,j));
        }
    }

    //����oriC���������
    for(int j=0;j<num;++j){
            if(j<n)StandardC.write(0,j,oriC.read(0,j));
            else StandardC.write(0,j,0);
        }


    //�����ɳڱ���ʹoriC��Ϊ��׼��ʽ��
    int k=0;
    for(int i=0;i<m;++i){
        if(p[i]>0){//���������ڵ�i�м���ϵ��-1
            Standard.write(i,n+k,1);
            for(int j=n;j<num;++j){
                if(j==(n+k)) continue;
                Standard.write(i,j,0);
            }
            ++k;
        }
        if(p[i]<0){//С�������ڵ�i�м���ϵ��1
            Standard.write(i,n+k,-1);
            for(int j=n;j<num;++j){
                if(j==(n+k))continue;
                Standard.write(i,j,0);
            }
            ++k;
        }
        if(p[i]==0){//���������ڲ���Ҫ�����˹�����
            for(int j=n;j<num;++j){
                Standard.write(i,j,0);
            }
        }
    }
    delete[]p;



    //����TwoPhase Method��Start Basis
    _Matrix Twophase(m,num+m),TwophaseC(1,num+m),TwophaseCB(1,m),TwophaseCT(1,num);
    for(int i=0;i<m;++i){
        TwophaseCB.write(0,i,-1);
    }
    for(int i=0;i<num;++i){
        TwophaseCT.write(0,i,0);
    }
    for(int j=0;j<num;++j){
            if(j<num)TwophaseC.write(0,j,StandardC.read(0,j));
            else TwophaseC.write(0,j,0);
        }
    for(int i=0;i<m;++i){
        for(int j=0;j<num;++j){
            Twophase.write(i,j,Standard.read(i,j));
        }
    }
    for(int i=0;i<m;++i){
        Twophase.write(i,i+num,1);
        for(int j=num;j<num+m;++j){
            if(j!=num+i) Twophase.write(i,j,0);
        }
    }



    //�ҳ�B��N��CBT(CB)��CNT(CT)��b��originalC������(��ԭʼĿ�꺯����ϵ������)
    _Matrix_Calc operate;
    _Matrix N(m,num),B(m,m),CN(num,1),CB(m,1),originalC(num,1);
    _Matrix BV(1,m),NBV(1,num);//����BV��NBV���±�
    for(int i=0;i<m;++i){
        BV.write(0,i,num+1+i);
    }
    for(int i=0;i<num;++i){
        NBV.write(0,i,i+1);
    }
    for(int i=0;i<m;++i){
        for(int j=0;j<num;++j){
            N.write(i,j,Standard.read(i,j));
        }
    }
    for(int i=0;i<m;++i){
        for(int j=0;j<m;++j){
            if(i==j) B.write(i,j,1);
            else B.write(i,j,0);
        }
    }
    for(int i=0;i<num;++i){
        CN.write(i,0,0);
    }
    for(int i=0;i<m;++i){
        CB.write(i,0,-1);
    }
    operate.transpos(&StandardC,&originalC);
    printf_matrix(&B);
    cout<<endl;
    printf_matrix(&N);
    cout<<endl;
    printf_matrix(&CB);
    cout<<endl;
    printf_matrix(&CN);
    cout<<endl;
    printf_matrix(&b);
    cout<<endl;
    printf_matrix(&NBV);
    cout<<endl;
    printf_matrix(&Twophase);
    cout<<endl;
    printf_matrix(&BV);
    cout<<endl;
    printf_matrix(&StandardC);
    //B(2,2),BV(1,2),NBV(1,5),N(2,5),CB(2,1),CN(5,1),b(2,1),StandardC(5,1);
    //NBV<=������NBV���������

    /*************************************/
    //��ʼsearching
    _Matrix originalBV=BV;
    _Matrix firstphaseRN(1,NBV.n),blandrules(1,BV.n);
    firstphaseRN=get_chekingnumber(CN,CB,B,N);
    float nameofentering,nameofleaving;
    int j1,p1;//jΪentering������pΪleaving����
    while(!is_nomorethan0(firstphaseRN))
    {
        j1=find_entering(firstphaseRN,NBV,nameofentering);
        blandrules=get_blandrules(B,b,N,j1);
        printf_matrix(&blandrules);
        if(is_unbounded(blandrules))
            {
                cout<<"sorry, the linear program is unbounded"<<endl;
                return 0;
            }
        p1=find_leaving(blandrules,BV,nameofleaving);
        changebvnbv(BV,NBV,j1,p1,nameofentering,nameofleaving);
        changebncbcn(B,N,CB,CN,j1,p1);
        firstphaseRN=get_chekingnumber(CN,CB,B,N);
        cout<<"entering->x"<<nameofentering<<endl;
        cout<<"leaving->x"<<nameofleaving<<endl;
        printf_matrix(&firstphaseRN);
    }
    if(is_nofeasiblesolution(BV,originalBV))//initiaBV,originalBV��Ӧ���ֲ�ȷ��������twophase���˹��������±�
    {
        cout<<"sorry,there is no feasible solution"<<endl;
        return 0;
    }
    //����ڶ���ǰ�ı�N��һϵ������
    _Matrix secondphaseCN((NBV.n-BV.n),1),secondphaseCB(BV.n,1),secondphaseN(N.m,(NBV.n-BV.n));
    _Matrix secondphaseRN(1,NBV.n-B.m),secondphaseNBV(1,(NBV.n-BV.n));
    secondphaseNBV=changesecondphaseNBV(NBV,BV,originalBV);
    secondphaseCN=changesecondphaseCN(NBV,BV,originalBV,originalC);
    secondphaseCB=changesecondphaseCB(BV,originalC);
    secondphaseN=changesecondphaseN(NBV,BV,originalBV,N);
    secondphaseRN=get_chekingnumber(secondphaseCN,secondphaseCB,B,secondphaseN);
    //����ڶ��׶�phase2
    cout<<"secondphase in progress"<<endl;
    secondphaseRN=get_chekingnumber(secondphaseCN,secondphaseCB,B,secondphaseN);
    cout<<"secondphaseNBV"<<endl;
    printf_matrix(&secondphaseNBV);
    cout<<"secondphaseN"<<endl;
    printf_matrix(&secondphaseN);
    cout<<"secondphaseCN"<<endl;
    printf_matrix(&secondphaseCN);
    cout<<"secondphaseCB"<<endl;
    printf_matrix(&secondphaseCB);
    cout<<"secondphaseRN"<<endl;
    printf_matrix(&secondphaseRN);
    while(!is_nomorethan0(secondphaseRN))
    {
        j1=find_entering(secondphaseRN,secondphaseNBV,nameofentering);
        blandrules=get_blandrules(B,b,secondphaseN,j1);
        if(is_unbounded(blandrules))
            {
                cout<<"sorry, the linear program is unbounded"<<endl;
                return 0;
            }
        p1=find_leaving(blandrules,BV,nameofleaving);
        changebvnbv(BV,secondphaseNBV,j1,p1,nameofentering,nameofleaving);
        changebncbcn(B,secondphaseN,secondphaseCB,secondphaseCN,j1,p1);
        secondphaseRN=get_chekingnumber(secondphaseCN,secondphaseCB,B,secondphaseN);
        cout<<"entering->x"<<nameofentering<<endl;
        cout<<"leaving->x"<<nameofleaving<<endl;
    }
    if(is_infinite(secondphaseRN))
        {
            cout<<"there is infinite solutions"<<endl;
        }
    printopt(secondphaseNBV,BV,b,B,secondphaseCB);
    return 0;
}