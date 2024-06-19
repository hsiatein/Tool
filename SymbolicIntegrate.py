import time

from sympy import *
from sympy.core.function import AppliedUndef
import re
from fractions import Fraction
x=Symbol('x')
c=Symbol('c')
secret=Symbol('secret')
def RemoveSameElements(a,b):
    temp_a = a.copy()
    temp_b = b.copy()
    for a in a:
        if a in b:
            temp_a.remove(a)
            temp_b.remove(a)
    return temp_a,temp_b
def derivate(a,expr):
    print(a)
    return secret*diff(expr,secret)/a+expr
class HGFunction:
    def __init__(self,a,b,expr):
        self.p=len(a)
        self.q=len(b)
        self.a=a
        self.b=b
        self.expr=expr
    def simplify(self):
        temp_a=self.a.copy()
        temp_b=self.b.copy()
        for a in self.a:
            if a in self.b:
                temp_a.remove(a)
                temp_b.remove(a)
        return HGFunction(temp_a,temp_b,self.expr)
    def display(self):
        # print(f"a={self.a}")
        # print(f"b={self.b}")
        # print(f"z={self.expr}")
        return f"F({self.a},{self.b},{self.expr})"
    def HGFtoF(self):
        z=self.expr
        a=self.a
        b=self.b
        if self.p==0 and self.q==0:
            return exp(z)
        elif self.p==1 and self.q==0:
            return pow(1-z,-a[0])
        elif self.p==0 and self.q==1:
            if z>=0:
                return besseli(b[0]-1,2*sqrt(z))*gamma(b[0])*z**(-Rational(b[0]-1,2))
            if z<0:
                z=-z
                return besselj(b[0]-1,2*sqrt(z))*gamma(b[0])*z**(-Rational(b[0]-1,2))
        elif self.p==1 and self.q==1:
            J=HGFunction._1F_1(a[0],b[0],z)
            if J!=None:
                return J
            else:
                J=HGFunction._1F_1(b[0]-a[0],b[0],-z)
                if J!=None:
                    return J*exp(z)
            return hyper(a,b,z)
        else:
            return hyper(a,b,z)
    @classmethod
    def _1F_1(cls,a,b,z):
        #print(f"a={a},b={b},z={z}")
        if (a-b).is_Integer:
            n = a - b
            if n >= 0:
                return gamma(b) * gamma(n + 1) / gamma(a) * exp(z) * assoc_laguerre(n, b - 1, -z)
            elif n == -1:
                if a == Rational(1, 2) and z<=0:
                    return sqrt(pi) * erf(sqrt(-z)) / 2 / sqrt(-z)
                elif a == Rational(1, 2) and z>0:
                    return sqrt(pi) * erfi(sqrt(z)) / 2 / sqrt(z)
                elif z<0:
                    return a * (-z) ** (-a) * lowergamma(a, -z)
                else:
                    return hyper([a],[b],z)
        temp = 2 * a- b
        if temp.is_Integer and temp>=0:
            n = floor(temp / 2)
            m = temp - 2 * n
            nu=a-n-Rational(1,2)
            expr=(secret/4)**(-nu)*exp(secret/2)*gamma(1+nu)*besseli(nu,secret/2)
            d_para_set=[a-n+i for i in range(n)]+[b+m-1-i for i in range(m)]
            #print(f"{n},{m},{d_para_set}")
            for d_para in d_para_set:
                expr=derivate(d_para,expr)
            return expr.subs(secret,z)
        #print("重算")
        return None

class MeijerG:
    #G(a,b,expr)
    def __init__(self,a_L,a_R,b_L,b_R,expr):
        self.m=len(b_L)
        self.n=len(a_L)
        self.p=self.n+len(a_R)
        self.q=self.m+len(b_R)
        self.a_L=a_L
        self.a_R=a_R
        self.b_L=b_L
        self.b_R=b_R
        self.a=a_L+a_R
        self.b=b_L+b_R
        self.expr=expr
    def display(self):
        # print("a=",self.a_L,self.a_R)
        # print("b=", self.b_L, self.b_R)
        # print("z=",self.expr)
        return f"G({self.a_L}{self.a_R},{self.b_L}{self.b_R},{self.expr})"
    def simplify(self):
        a_L,b_R=RemoveSameElements(self.a_L,self.b_R)
        a_R,b_L=RemoveSameElements(self.a_R,self.b_L)
        M=MeijerG(a_L,a_R,b_L,b_R,self.expr)
        if M.p>M.q:
            return MeijerG([1-b for b in M.b_L],[1-b for b in M.b_R],
                           [1-a for a in M.a_L],[1-a for a in M.a_R],Rational(1,M.expr))
        else:
            return M
    @classmethod
    def FtoG(cls,FuncAndArgs):
        if FuncAndArgs[0]=='exp':
            return [1,MeijerG([],[],[0],[],(-1)*FuncAndArgs[1][0])]
        elif FuncAndArgs[0]=='sin':
            return [sqrt(pi),MeijerG([],[],[Rational(1,2)],[0],Rational(1,4)*FuncAndArgs[1][0]**2)]
        elif FuncAndArgs[0]=='cos':
            return [sqrt(pi), MeijerG([], [], [0],[Rational(1,2)], Rational(1,4) * FuncAndArgs[1][0] ** 2)]
        elif FuncAndArgs[0] == 'cosh':
            return [sqrt(pi), MeijerG([], [], [0], [Rational(1,2)], (-Rational(1,4)) * FuncAndArgs[1][0] ** 2)]
        elif FuncAndArgs[0]=='sinh':
            return [-sqrt(pi)*I, MeijerG([], [], [Rational(1,2)],[0], (-Rational(1,4)) * FuncAndArgs[1][0] ** 2)]
        elif FuncAndArgs[0]=='ModifiedHeaviside1':
            return [1, MeijerG([], [1], [0], [], FuncAndArgs[1][0])]#H(x)=1,x<1,0,x>1
        elif FuncAndArgs[0]=='ModifiedHeaviside2':
            return [1, MeijerG([1], [], [], [0], FuncAndArgs[1][0])]#H(x)=0,x<1,1,x>1
        elif FuncAndArgs[0]=='besselj':
            return [1, MeijerG([], [], [Rational(FuncAndArgs[1][0],2)], [-Rational(FuncAndArgs[1][0],2)]
                               , Rational(1,4) * FuncAndArgs[1][1] ** 2)]
        elif FuncAndArgs[0]=='bessely':
            return [1, MeijerG([], [-Rational(FuncAndArgs[1][0]+1, 2)],
                               [Rational(FuncAndArgs[1][0], 2),-Rational(FuncAndArgs[1][0], 2)],
                               [-Rational(FuncAndArgs[1][0]+1, 2)]
                               , Rational(1, 4) * FuncAndArgs[1][1] ** 2)]
        elif FuncAndArgs[0]=='besseli':
            return [I**(-FuncAndArgs[1][0]), MeijerG([], [], [Rational(FuncAndArgs[1][0],2)],
                                                     [-Rational(FuncAndArgs[1][0],2)]
                               , -Rational(1,4) * FuncAndArgs[1][1] ** 2)]
        elif FuncAndArgs[0]=='besselk':
            return [Rational(1,2), MeijerG([], [], [Rational(FuncAndArgs[1][0],2),-Rational(FuncAndArgs[1][0],2)],
                                           [], Rational(1,4) * FuncAndArgs[1][1] ** 2)]
    def GtoHGF(self):
        def GammaProd(array, x, type=0):
            G = 1
            # print(array)
            if type == 0:
                for a in array:
                    #print(a + x)
                    G = G * gamma(Rational(a + x))
            elif type == 1:
                for a in array:
                    G = G * gamma(Rational(-a + x))
            return G
        M=self.simplify()
        M.display()
        total = []
        for h in range(0,M.m):
            bh=M.b_L[h]
            coe=M.expr**bh*GammaProd(M.b_L[:h]+M.b_L[h+1:],-bh)*GammaProd(M.a_L,1+bh,1)\
                /GammaProd(M.b_R,1+bh,1)/GammaProd(M.a_R,-bh)
            #print(f"coe={M.expr**bh}")
            HGF=HGFunction([1+bh-a for a in M.a],[1+bh-b for b in M.b[:h]+M.b[h+1:]],
                           Pow(-1,M.p-M.m-M.n)*M.expr).simplify()
            total.append([coe,HGF])
            HGF.display()
        return total


def parse_expression(expr):
    # 将字符串表达式转换为 SymPy 的表达式对象
    expr=expand_trig(expr)
    expr=expand_power_exp(expr)
    expr = expand(expr)
    # 提取每个项并构成一个数组
    if isinstance(expr, Add):
        terms = expr.args
    else:
        terms = [expr]
    # 打印每个项
    total_func_arg=[]
    for term in terms:
        #print(f"项: {term}")
        # 提取每个项并构成一个数组
        if isinstance(term, Mul):
            temps = list(term.args)
            if not temps[0].is_Number:
                temps=[1]+temps
        else:
            temps = [1,term]
        temps_modified=[1]
        for t in temps:
            if x not in sympify(t).free_symbols:
                temps_modified[0]=temps_modified[0]*t
            else:
                temps_modified.append(t)
        temps=temps_modified
        #print(temps)
        functions = [temps[0]]
        for temp in temps[1:]:
            if temp==x:
                functions.append(['Pow',(x, 1)])
            else:
                functions.append([temp.func.__name__, temp.args])
        if len(functions)==1:
            functions.append(['Pow', (x, 0)])
        if functions[1][0]!='Pow':
            functions=[functions[0]]+[['Pow', (x, 0)]]+functions[1:]
        total_func_arg.append(functions)
    #print(total_func_arg)
    return total_func_arg
def Integrate(raw_expr,x0=0,x1=oo,print_process=False):
    print(f"积分{raw_expr}从{x0}到{x1}:")
    log=""
    time1=time.time()
    def GammaProd(array,x,type=0):
        G=1
        #print(array)
        if type == 0:
            for a in array:
                G=G*gamma(Rational(a+x))
        elif type==1:
            for a in array:
                G=G*gamma(Rational(-a+x))
        return G
    terms=parse_expression(str(raw_expr))
    log=log+f"得到解析后的表达式\r\n{terms}\r\n"
    I=0
    if x0 == 0 and x1 == oo:
        pass
    elif x0 == 0 and x1 != oo:
        for term in terms:
            term.append(['ModifiedHeaviside1', (Rational(1, x1) * x,)])
    elif x0 != 0 and x1 == oo:
        for term in terms:
            term.append(['ModifiedHeaviside2', (Rational(1, x0) * x,)])
    else:
        tempterm=[term.copy() for term in terms]
        for term1 in tempterm:
            term1[0]=-term1[0]
            term1.append(['ModifiedHeaviside1', (Rational(1, x0) * x,)])
        for term2 in terms:
            term2.append(['ModifiedHeaviside1', (Rational(1, x1) * x,)])
        terms=terms+tempterm
    #print(terms)
    for term in terms:
        log = log + f"此步积分为{term}\r\n"
        if len(term)==3:
            temp=MeijerG.FtoG(term[2])
            log=log+f"{term[2]}转换成{temp[0]}*{temp[1].display()}\r\n"
            #print(temp)
            gamma1=temp[1].expr.as_poly(x).degree()
            beta1=temp[1].expr.coeff(x**gamma1)
            #print(temp[1].a,",",temp[1].b)
            s=term[1][1][1]
            #print(f"beta={beta1},gamma={gamma1},s={s},系数={term[0]*temp[0]}")
            log = log +f"beta={beta1},gamma={gamma1},s={s},系数={term[0]*temp[0]}\r\n"
            J=term[0]*temp[0]*beta1**(-Rational(s+1,gamma1))*GammaProd(temp[1].b_L,Rational(s+1,gamma1))\
              *GammaProd(temp[1].a_L,1-Rational(s+1,gamma1),1)\
              /GammaProd(temp[1].b_R,1-Rational(s+1,gamma1),1)\
              /GammaProd(temp[1].a_R,Rational(s+1,gamma1))/gamma1
            #log= log +f"{GammaProd(temp[1].b_L,Rational(s+1,gamma1))}"
            #print(latex(J))
            #print(f"J={J}")
            log = log + f"此步积分结果{J}\r\n"
            I=I+J
        if len(term)==4:
            #print(term)
            nu=term[1][1][1]+1
            M1 = MeijerG.FtoG(term[2])
            M2=MeijerG.FtoG(term[3])
            log = log + f"{term[2]}转换成{M1[0]}*{M1[1].display()}\r\n"
            log = log + f"{term[3]}转换成{M2[0]}*{M2[1].display()}\r\n"
            gamma1 = M1[1].expr.as_poly(x).degree()
            beta1 = M1[1].expr.coeff(x ** gamma1)
            gamma2 = M2[1].expr.as_poly(x).degree()
            beta2 = M2[1].expr.coeff(x ** gamma2)
            coe=term[0] * M1[0]*M2[0]
            #print(f"beta1={beta1},gamma1={gamma1},beta2={beta2},gamma2={gamma2},nu={nu}")
            log = log + f"beta1={beta1},gamma1={gamma1},beta2={beta2},gamma2={gamma2},nu={nu}\r\n"
            k=lcm(gamma1,gamma2)
            h1=Rational(k,gamma1)
            h2=Rational(k,gamma2)
            expr=Rational(beta1**h1*h1**(h1*(len(M1[1].a)-len(M1[1].b))),beta2**h2*h2**(h2*(len(M2[1].a)-len(M2[1].b))))
            #print(f"k={k},h1={h1},h2={h2},expr={expr}")
            log = log +f"k={k},h1={h1},h2={h2},expr={expr}\r\n"
            coe=coe*(2*pi)**(Rational(1-h1,2)*(len(M1[1].a_L)+len(M1[1].b_L)-len(M1[1].a_R)-len(M1[1].b_R))
                             +Rational(1-h2,2)*(len(M2[1].a_L)+len(M2[1].b_L)-len(M2[1].a_R)-len(M2[1].b_R)))\
                *h1**(sum(M1[1].b)-sum(M1[1].a)+Rational(1,2)*(len(M1[1].a)-len(M1[1].b)))\
                *h2**(sum(M2[1].b)-sum(M2[1].a)+(Rational(1,2)-Rational(nu,gamma2))*(len(M2[1].a)-len(M2[1].b)))\
                *beta2**(-Rational(nu,gamma2))*k/gamma1/gamma2
            # print(f"M1:aL={M1[1].a_L},aR={M1[1].a_R},bL={M1[1].b_L},bR={M1[1].b_R}")
            # print(f"M2:cL={M2[1].a_L},cR={M2[1].a_R},dL={M2[1].b_L},dR={M2[1].b_R}")
            # print(f"系数{coe}")
            A_L=[]
            A_R=[]
            B_L=[]
            B_R=[]
            for i in range(h1):
                A_L=A_L+[1+Rational(a-i-1,h1) for a in M1[1].a_L]
                A_R = A_R + [Rational(a + i, h1) for a in M1[1].a_R]
                B_L=B_L+ [Rational(b + i, h1) for b in M1[1].b_L]
                B_R=B_R+[1+Rational(b-i-1,h1) for b in M1[1].b_R]
            for i in range(h2):
                A_L = A_L + [1-Rational(nu,k) - Rational(d+i, h2) for d in M2[1].b_L]
                A_R=A_R + [-Rational(nu,k)+Rational(-d+1+i, h2) for d in M2[1].b_R]
                B_L = B_L +[-Rational(nu,k)+Rational(-c+1+i, h2) for c in M2[1].a_L]
                B_R = B_R +[1-Rational(nu,k) - Rational(c+i, h2) for c in M2[1].a_R]
            #MeijerG(A_L, A_R, B_L, B_R, expr).display()
            M_integrate=MeijerG(A_L,A_R,B_L,B_R,expr).simplify()
            log=log+f"积分后的MeijerG:{coe}*{M_integrate.display()}\r\n"
            #M_integrate.display()
            HGFs=M_integrate.GtoHGF()
            J=0
            for HGF in HGFs:
                #print(HGF[0])
                log = log + f"化归超几何{coe*HGF[0]}{HGF[1].display()}\r\n"
                J=J+HGF[0]*HGF[1].HGFtoF()
                log = log + f"化简{coe * HGF[0]*HGF[1].HGFtoF()}\r\n"
            I=I+coe*J
    I=expand(I)
    #print(f"{raw_expr}从0到\infty积分为{I}\r\n耗时{time.time()-time1},数值值{I.evalf()}")
    if print_process:
        print(log)
    print(f"最终结果{I}\r\n数值值{I.evalf()},耗时{time.time()-time1}\r\n")
    return I





Integrate(exp(-5*x**2)*cos(x+4))
Integrate(exp(-3*x)*cos(x))
Integrate(x*besselj(2,x)*besselj(1,x**2))
Integrate(besselk(Rational(1,2),x)*sin(x))
Integrate(x**2*exp(-x**2)*besselj(2,x),0,oo,True)
Integrate(exp(-x**2)*besselj(2,x))
Integrate(exp(-x**2)*besselk(Rational(1/2),x))
Integrate(exp(-x)*besselj(0,5*x))
Integrate(exp(-x),1,5)
Integrate((x+1+x**2)**5,1,5)

# time1=time.time()
# print(integrate(x*besselj(2,x)*besselj(1,x**2),(x,0,oo)))
# time2=time.time()
# print(f"耗时{time2-time1}")
# print(integrate(exp(-x**2)*besselj(2,x),(x,0,oo)))
# time3=time.time()
# print(f"耗时{time3-time2}")
# print(integrate(exp(-x**2)*besselk(Rational(1/2),x),(x,0,oo)))
# print(f"耗时{time.time()-time3}")