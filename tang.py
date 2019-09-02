import random
import math
from math import sqrt
import uuid
from mpmath import *
from fractions import Fraction as frac
from fractions import *
from decimal import *
import sys
import sympy
import os
import time
from os import *
from binascii import *
import hashlib
import secrets
from functools import reduce
import timeit
import matplotlib.pyplot as plt
import numpy as np
#### DEFINITIONS ####
def concatenate_list_data(list): #concatenation
    result=''
    for element in list:
        result += str(element)
    return result
def extended_gcd(aa, bb): #Extended Euclidean algorithm
    lastremainder, remainder = abs(aa), abs(bb)
    x, lastx, y, lasty = 0, 1, 1, 0
    while remainder:
        lastremainder, (quotient, remainder) = remainder, divmod(lastremainder,\
                                                                 remainder)
        x, lastx = lastx - quotient*x, x
        y, lasty = lasty - quotient*y, y
    return lastremainder, lastx * (-1 if aa < 0 else 1), lasty * (-1 if bb < 0 \
                                                                  else 1)
 
def modinv(a, m): #Modular Inverse via the use of the Ext. Euclid. Alg.
    g, x, y = extended_gcd(a, m)
    if g != 1:
        raise ValueError
    return x % m
def tang():
    ##### Preliminary step to establish parameters #####
    p=int("AC6BDB41324A9A9BF166DE5E1389582FAF72B6651987EE07FC3192943DB56050A37\
329CBB4A099ED8193E0757767A13DD52312AB4B03310DCD7F48A9DA04FD50E8083969EDB767B0CF\
6095179A163AB3661A05FBD5FAAAE82918A9962F0B93B855F97993EC975EEAA80D740ADBF4FF747\
359D041D5C33EA71D281E446B14773BCA97B43A23FB801676BD207A436C6481F1D2B9078717461A\
5B9D32E688F87748544523B524B0D57D5EA77A2775D2ECFA032CFBDBF52FB3786160279004E57AE\
6AF874E7303CE53299CCC041C7BC308D82A5698F3A8D0C38271AE35F8E9DBFBB694B5C803D89F7A\
E435DE236D525F54759B65E372FCD68EF20FA7111F9E4AFF73", 16)
    #p is a safe prime, p=2q+1, from SRP: http://www.ietf.org/rfc/rfc5054.txt
    #print(sympy.isprime(p)) #checks if p is definitely prime
    q=(p-1)//2  #integer form of q 
    #print(sympy.isprime(q)) #checks if q is definitely prime
    qbin="{0:b}".format(q-1) #binary form of q
    exponent_size=len(qbin)

    #password - low entropy
    pi="dictionary"

    #Group Identifier
    ID=[]
    for i in range(0,n):
        ID.insert(i,int.from_bytes(os.urandom(256),byteorder="big"))
        #ID_i is some random integer in the 2048-bit (256 byte) modulus
    #print(ID)
    concatID=concatenate_list_data(ID)
        
    #Generator g
    xstr='0'
    x=0
    concat1=concatID+pi+xstr
    #print(concat1)
    g=hashlib.sha256(b'concat1')
    #g=H_0(pi||ID_u||x)
    #g is the concatenation of IDu, password, and some padding element x
    g=(int(g.hexdigest(),16))%p
    #check to see if g needs padding with an integer, x, to make into a
    #generator
    for x in range(0,p):
        if (g**((p-1)//q)%p)!=1:
            #print('This is a generator')
            #if this = 1, g is not a generator, if != 1, g is a generator
            break
        else:
            #loops until the right value of x is found to ensure g is a
            #generator
            x += 1
            xstr=str(x)
            concat1=concatID+pi+xstr
            g=hashlib.sha256(b'concat1') #g=H(IDu|pwd|x)
            g=int(g.hexdigest(),16)

    ##### Main Protocol #####
    ####ROUND ONE####
    ###Z_i COMPUTATION###
    s=[]
    Z=[]
    for i in range(0,n):
        s.insert(i,secrets.randbits(exponent_size))
        #secrets generates secure RN - can define a range as
        Z.insert(i,pow(g,s[i],p))
        #pow function fastest method in python to compute exp.
        #Z_i=g^(s_i) mod p, Z_i is broadcasted
    #print(Z)

    ###Z_i VERIFICATION###
    for i in range (0,n):
        for j in range(0,n):
            if j == i:
                continue
            #checking values g^(s_j) for all j not equal to i
            #(no need to check own value)
            if j != i:
                if Z[j] == 1:
                    print('Verification failed from participant', j)
                    #This informs of which participants values caused failed
                    #verification
                    sys.exit()
                    #terminate protocol if verification fails,
                if Z[j] != 1:
                    #print('Verification successful from participant', j)
                    j += 1

    ####ROUND TWO####
    ###A_i-1 AND A_i+1 COMPUTATION###
    concatZ=concatenate_list_data(Z) #Z=Z_1 || ... || Z_n
    #print(Zu)
    exp1c=[]
    exp2c=[]
    concat2c=[]
    concat3c=[]
    a1c=[]
    a2c=[]
    A1c=[]
    A2c=[]
    for i in range(0,n): #A_(i,i-1) & A_(i,i+1)
        exp1c.insert(i,pow(Z[i],s[(i-1)%n],p)) #g^(s_i s_i-1)
        exp2c.insert(i,pow(Z[i],s[(i+1)%n],p)) #g^(s_i s_i+1)
        concat2c.insert(i,str(i)+str(((i-1)%n))+concatZ+str(exp1c[i])+str(g)\
                        +concatID) #First, the concatenation
        concat3c.insert(i,str(i)+str(((i+1)%n))+concatZ+str(exp2c[i])+str(g)\
                        +concatID)
        a1c.insert(i,hashlib.sha256(concat2c[i].encode()))
        #Then the sha256 hash of the concatenated input
        a2c.insert(i,hashlib.sha256(concat3c[i].encode()))
        A1c.insert(i,int(a1c[i].hexdigest(),16))
        #Then need to make this an integer rather than a hex value
        A2c.insert(i,int(a2c[i].hexdigest(),16))
        #A1c_i and A2c_i are broadcast at the end of the round

    ###A_i-1 AND A_i+1 VERIFICATION###
    exp1v=[[] for x in range(n)]
    exp2v=[[] for x in range(n)]
    concat2v=[[] for x in range(n)]
    concat3v=[[] for x in range(n)]
    a1v=[[] for x in range(n)]
    a2v=[[] for x in range(n)]
    A1v=[[] for x in range(n)]
    A2v=[[] for x in range(n)]
    #NB: This is creating 8 lists for each participant, therefore, as loop
    #through i, the previous ith participants list is removed.
    for i in range(0,n):
        for j in range(0,n):
            if j == i:
                exp1v[i].insert(j,0)
                #This is to show that participant i does not need to check
                #their own computation within their row in the
                #multi-dimensional list
                exp2v[i].insert(j,0)
                concat2v[i].insert(j,0)
                concat3v[i].insert(j,0)
                a1v[i].insert(j,0)
                a2v[i].insert(j,0)
                A1v[i].insert(j,0)
                A2v[i].insert(j,0)
                continue
            #P_i is checking values, A_(i-1,i) and A_(i+1,i)
            #(no need to check own value)
            if j != i:
                concat2v[i].insert(j,str(j)+str(((j-1)%n))+concatZ+str(exp1c[j])\
                                   +str(g)+concatID) #First, the concatenation
                concat3v[i].insert(j,str(j)+str(((j+1)%n))+concatZ+str(exp2c[j])\
                                   +str(g)+concatID)
                a1v[i].insert(j,hashlib.sha256(concat2v[i][j].encode()))
                #Then the sha256 hash of the concatenated input
                a2v[i].insert(j,hashlib.sha256(concat3v[i][j].encode()))
                A1v[i].insert(j,int(a1v[i][j].hexdigest(),16))
                #Then need to make this an integer rather than a hex value
                A2v[i].insert(j,int(a2v[i][j].hexdigest(),16))
                if A1v[i][j] != A1c[j]:
                    #Verification values must equal computed value for
                    #protocol to proceed
                    print('Verification failed from participant', j)
                    sys.exit()
                if A2v[i][j] != A2c[j]:
                    print('Verification failed from participant', j)
                    sys.exit()
                if A1v[i][j] == A1c[j] and A2v[i][j] == A2c[j]:
                    #print('Verication successful from participant', j)
                    j += 1
    #print(A1v)
    #print(A2v)

    ####ROUND THREE####
    ###X_i COMPUTATION###
    numerator1=[]
    denominator1=[]
    invZ=[]
    X=[]
    for i in range(0,n):
        numerator1.insert(i,pow(Z[(i+1)%n],s[i],p))
        denominator1.insert(i,pow(Z[(i-1)%n],s[i],p))
        invZ.insert(i,modinv(denominator1[i],p))
        X.insert(i,(numerator1[i]*invZ[i])%p)
        #X_i=(Z_(i+1)/Z_(i-1))^(s_i)
        #X_i is broadcasted at the end of the round
    #print(invZ) 
    #inv1=modinv(denominator[0],p)
    #print(inv1)

    ####ROUND FOUR####
    ###KEYING MATERIAL COMPUTATION###
    M=[]
    exp3c=[]
    exp4c=[[] for x in range(n)]
    prod1=[]
    for i in range(0,n):
        exp3c.insert(i,pow(Z[(i-1)%n],n*s[i],p))
        for j in range(0,n-1):
            exp4c[i].insert(j,pow(X[(i+j)%n],(n-1-j),p)) 
        prod1.insert(i,reduce((lambda x, y: x * y),exp4c[i]))
        #prod_(j=0)^(n-2){[X_(i+j)]^(n-1-j)}
        M.insert(i,(exp3c[i]*prod1[i])%p)
        #M=(Z_(i-1)^(ns_i))*\prod_(j=1)^(n-1) (X_(i+j)^(n-1-j))
    #print(exp3c)
    #print(exp4c)
    #print(M)    

    ###KEY CONFIRMATION MESSAGE COMPUTATION###
    concatCc=[]
    hashCc=[]
    Cc=[]
    concatX=concatenate_list_data(X)
    concatA=concatenate_list_data(A2c)+concatenate_list_data(A1c)
    for i in range(0,n):
        concatCc.insert(i,str(i)+concatID+concatZ+concatA+concatX+str(M[i])\
                        +str(g))
        hashCc.insert(i,hashlib.sha256(concatCc[i].encode()))
        Cc.insert(i,int(hashCc[i].hexdigest(),16))
        #C_i = H_1(i||ID_u||Z||A||X||M_i||g)
        #Cc_i is broadcasted at the end of this round

    ###KEY CONFIRMATION MESSAGE VERIFICATION###
    concatCv=[[] for x in range(n)]
    hashCv=[[] for x in range(n)]
    Cv=[[] for x in range(n)]
    for i in range(0,n):
        for j in range(0,n):
            if j == i:
                concatCv[i].insert(j,0)
                #This is to show that participant i does not need to check
                #their own computation within their row in the
                #multi-dimensional list
                hashCv[i].insert(j,0)
                Cv[i].insert(j,0)
                continue
            if j != i:
                concatCv[i].insert(j,str(j)+concatID+concatZ+concatA+concatX+\
                                   str(M[i])+str(g))
                hashCv[i].insert(j,hashlib.sha256(concatCv[i][j].encode()))
                Cv[i].insert(j,int(hashCv[i][j].hexdigest(),16))
                if Cv[i][j] != Cc[j]:
                    #verification values must equal computed value for
                    #protocol to proceed
                    print('Verification failed from participant', j)
                    sys.exit()
                if Cv[i][j] == Cc[j]:
                    #print('Verication successful from participant', j)
                    j += 1

    ###SESSION KEY COMPUTATION###
    concatK=[]
    hashK=[]
    K=[]
    for i in range(0,n):
        concatK.insert(i,concatID+concatZ+concatA+concatX+str(M[i]))
        hashK.insert(i,hashlib.sha256(concatK[i].encode()))
        K.insert(i,int(hashK[i].hexdigest(),16))
        #K_i=H_2(ID_u||Z||A||X||M)
    #print(K)
    #SID defined to be the concatenation of identities, and all broadcasted
    #messages (Z_i,A_(i,i-1),A_(i,i+1),X_i,C_i)
    concatC=concatenate_list_data(Cc)
    SID=concatID+concatZ+concatA+concatX+concatC
    #Session Identifier
    #print(SID)

    #QUICK CHECK:
    #for i in range(0,n):
    #    if K[i] == K[(i+1)%n]:
    #        print("Equal Keys", i)
    #        i += 1


latency=[]
n=3
for n in range(3,10):
    start=time.time()
    tang()
    end=time.time()
    latency.insert(n,end-start)
    n += 1
print(latency)
n = [str(i) for i in range(3,21)]
print(n)


def bar_plot():
    plt.bar(n,latency)
    plt.xlabel('No. of Participants in the group')
    plt.ylabel('Latency (s)')
    plt.title('Latency Measurements in Tang & Choo Protocol \
(p=2048, hash=SHA256)')
    plt.show()
bar_plot()

