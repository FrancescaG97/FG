import random
import math
from math import sqrt
from math import floor
from math import ceil
import uuid
from mpmath import *
from fractions import Fraction as frac
from fractions import *
from decimal import *
import sys
import sympy
import os
import os.path
from os import listdir
from os.path import isfile, join
import time
from os import *
from binascii import *
import hashlib
import base64
import secrets
from functools import reduce
import timeit
import matplotlib.pyplot as plt
import numpy as np
from Cryptodome.Cipher import AES
from Cryptodome import Random
from Cryptodome.Random import get_random_bytes
import json
from base64 import b64encode
from base64 import b64decode
#### DEFINITIONS ####
def concatenate_list_data(list): #concatenation
    result=''
    for element in list:
        result += str(element)
    return result
def bitstring_to_bytes(s):
    return int(s, 2).to_bytes(len(s) // 8, byteorder='big')
def int_to_bytes(x: int) -> bytes:
    return x.to_bytes((x.bit_length() + 7) // 8, 'big')
def extended_gcd(aa, bb):
    lastremainder, remainder = abs(aa), abs(bb)
    x, lastx, y, lasty = 0, 1, 1, 0
    while remainder:
        lastremainder, (quotient, remainder) = remainder, divmod(lastremainder,\
                                                                 remainder)
        x, lastx = lastx - quotient*x, x
        y, lasty = lasty - quotient*y, y
    return lastremainder, lastx * (-1 if aa < 0 else 1), lasty * (-1 if bb < 0 \
                                                                  else 1)
def modinv(a, m):
    g, x, y = extended_gcd(a, m)
    if g != 1:
        raise ValueError
    return x % m
class AESCipher:
    def __init__(self,key):
        self.key = hashlib.sha256(key.encode('utf-8')).digest()
        #self.key = key
    def encrypt(self, raw):
        raw = pad(raw)
        iv = Random.new().read(AES.block_size)
        cipher = AES.new(self.key, mode, iv)
        return base64.b64encode(iv + cipher.encrypt(raw.encode('utf-8')))
    def decrypt(self,enc):
        enc = base64.b64decode(enc)
        iv=enc[:16]
        cipher = AES.new(self.key, mode, iv)
        return unpad(cipher.decrypt(enc[16:]))
block_size = 16
pad = lambda s: s + (block_size - len(s) % block_size) * chr(block_size - len(s)\
                                                             % block_size)
unpad = lambda s: s[0:-s[-1]]
mode = AES.MODE_CBC
def ABCD():
    ##### Preliminary step to establish parameters #####
    p=int("AC6BDB41324A9A9BF166DE5E1389582FAF72B6651987EE07FC3192943DB56050A37\
329CBB4A099ED8193E0757767A13DD52312AB4B03310DCD7F48A9DA04FD50E8083969EDB767B0CF\
6095179A163AB3661A05FBD5FAAAE82918A9962F0B93B855F97993EC975EEAA80D740ADBF4FF747\
359D041D5C33EA71D281E446B14773BCA97B43A23FB801676BD207A436C6481F1D2B9078717461A\
5B9D32E688F87748544523B524B0D57D5EA77A2775D2ECFA032CFBDBF52FB3786160279004E57AE\
6AF874E7303CE53299CCC041C7BC308D82A5698F3A8D0C38271AE35F8E9DBFBB694B5C803D89F7A\
E435DE236D525F54759B65E372FCD68EF20FA7111F9E4AFF73", 16)
    #print(p)
    #p is a safe prime
    #print(sympy.isprime(p)) #checks if p is definitely prime
    q=(p-1)//2  #integer form of q
    g=int("A59A749A11242C58C894E9E5A91804E8FA0AC64B56288F8D47D51B1EDC4D65444FECA\
0111D78F35FC9FDD4CB1F1B79A3BA9CBEE83A3F811012503C8117F98E5048B089E387AF6949BF878\
4EBD9EF45876F2E6A5A495BE64B6E770409494B7FEE1DBB1E4B2BC2A53D4F893D418B7159592E4FF\
FDF6969E91D770DAEBD0B5CB14C00AD68EC7DC1E5745EA55C706C4A1C5C88964E34D09DEB753AD41\
8C1AD0F4FDFD049A955E5D78491C0B7A2F1575A008CCD727AB376DB6E695515B05BD412F5B8C2F4C\
77EE10DA48ABD53F5DD498927EE7B692BBBCDA2FB23A516C5B4533D73980B2A3B60E384ED200AE21\
B40D273651AD6060C13D97FD69AA13C5611A51B9085", 16)
    #2048-bit p, 2048-bit g and 2047-bit q values directed to use by NIST
    qbin="{0:b}".format(q-1)
    exponent_size=len(qbin)

    #password - low entropy
    pw="dictionary"


    ###MAIN PROTOCOL###
    ###ROUND 1###
    ###SESSION IDENTIFIER, S###
    ID=[]
    Nonce=[]
    S_p=[]
    for i in range(0,n):
        ID.insert(i,int.from_bytes(os.urandom(256),byteorder="big"))
        #ID_i is some random participant identifier of 2048-bits
        Nonce.insert(i,int.from_bytes(os.urandom(256),byteorder="big"))
        #Each participant selects some random nonce of 2048-bit
        S_p.insert(i,ID[i]+Nonce[i])
        #Each participant broadcasts S_p_i such that S can be computed
    S=concatenate_list_data(S_p)
    #print(ID)
    #print(Nonce)
    #print(S_p)
    #print(S)


    ###SYMMETRIC KEY DERIVATION###
    concat1=[]
    hashkeys=[]
    keys=[]
    string_keys=[]
    binary_keys=[]
    for i in range(0,n):
        concat1.insert(i,S+str(i)+pw) 
        #Assuming the input of the hash function is a concatenation of S,i
        #and the group pwd

    ###ROUND 2###
    ###Z_i COMPUTATION###
    x=[]
    z=[]
    strZ=[]
    for i in range(0,n):
        x.insert(i,secrets.randbits(exponent_size))
        #Random exponent value in range [1,q-1]
        z.insert(i,pow(g,x[i],p)) #z_i=g^(x_i)
        strZ.insert(i,str(z[i]))
        #AES encryption in python only works on strings
    iv=[]
    cipher=[]
    encryptZ=[]
    for i in range(0,n):
        iv.insert(i,Random.new().read(AES.block_size))
        #initialisation vector for AES256 encryption
        cipher.insert(i,AESCipher(concat1[i])) #P_i symmetric encryption key
        encryptZ.insert(i,cipher[i].encrypt(strZ[i])) #z_i^*
    #print(encryptZ)

    ###DECRYPTION AND X_i COMPUTATION###
    #compute j /neq i keys first, then decrypt
    cipher1=[]
    cipher2=[]
    decryptZ=[[] for x in range(n)]
    invZ=[]
    X=[]
    expZ=[[] for x in range(n)]
    for i in range(0,n):
        cipher1.insert(i,AESCipher(S+str((i-1)%n)+pw))
        #need to work out the encryption 
        cipher2.insert(i,AESCipher(S+str((i+1)%n)+pw))
        #keys for each neighbour
        decryptZ[i].insert(0,cipher1[i].decrypt(encryptZ[(i-1)%n]))
        #decrypt only the results from P_(i-1) and P_(i+1)
        decryptZ[i].insert(1,cipher2[i].decrypt(encryptZ[(i+1)%n]))                   
        expZ[i].insert(0,pow(int(decryptZ[i][0]),x[i],p)) #Z_i
        expZ[i].insert(1,pow(int(decryptZ[i][1]),x[i],p))#Z_(i-1)
        invZ.insert(i,modinv(expZ[i][0],p)) #X_i=Z_(i+1)/Z_(i)
        X.insert(i,(expZ[i][1]*invZ[i])%p)
    #print(strZ)
    ##print(expZ)
    #print(invZ)
    #print(X)
    #print(decryptZ)

    ###ROUND 3 - COMPUTATION###
    expZ1=[]
    expX=[[] for x in range(n)]
    prodK=[]
    K=[]
    concatZ=concatenate_list_data(z)
    concatEncrypt=concatenate_list_data(encryptZ)
    concatX=concatenate_list_data(X)
    concat2c=[]
    Auth_hash_c=[]
    Auth_c=[]
    for i in range(0,n):
        expZ1.insert(i,pow(expZ[i][0],n,p))
        #K=Z_i^nX_i^(n-1)X_(i+1)^(n-2)...X_(i+n-2)
        for j in range(0,n-1):
            expX[i].insert(j,pow(X[(i+j)%n],(n-j-1),p))
        prodK.insert(i,reduce((lambda x,y: x * y),expX[i]))
        K.insert(i,(prodK[i]*expZ1[i])%p)
    for i in range(0,n):
        concat2c.insert(i,S+concatEncrypt+concatX+str(K[i])+str(i))
        Auth_hash_c.insert(i,hashlib.sha256(concat2c[i].encode()))
        #Broadcast authentication tag
        Auth_c.insert(i,int(Auth_hash_c[i].hexdigest(),16))
        #so other Ps can verify          
    #print(expZ1)
    #print(expX)
    #print(prodK)
    #print(K)

    ###ROUND 3 - VERIFICATION###
    concat2v=[[] for x in range(n)]
    Auth_hash_v=[[] for x in range(n)]
    Auth_v=[[] for x in range(n)]
    for i in range(0,n):
        for j in range(0,n):
            if j == i:
                concat2v[i].insert(j,0)
                #This is to show that participant i does not need to check
                #their own computation within their row in the multi-dimensional
                #list
                Auth_hash_v[i].insert(j,0)
                Auth_v[i].insert(j,0)
                continue
            if j != i:
                concat2v[i].insert(j,S+concatEncrypt+concatX+str(K[j])+str(j))
                Auth_hash_v[i].insert(j,hashlib.sha256(concat2v[i][j].encode()))
                Auth_v[i].insert(j,int(Auth_hash_v[i][j].hexdigest(),16))
                if Auth_v[i][j] != Auth_c[j]:
                    print('Verification failed from participant', j)
                    sys.exit()
                if Auth_v[i][j] == Auth_c[j]:
                    #print('Verication successful from participant', j)
                    j += 1

    ###SESSION KEY COMPUTATION###
    concatAuth=concatenate_list_data(Auth_c)
    concat3=[]
    sk_hash=[]
    SK=[]
    for i in range(0,n):
        concat3.insert(i,S+concatEncrypt+concatX+concatAuth+str(K[i]))
        sk_hash.insert(i,hashlib.sha256(concat3[i].encode()))
        SK.insert(i,int(sk_hash[i].hexdigest(),16))
    #print(SK)
    #quick check#
    #for i in range(0,n):
    #    if SK[i] == SK[(i+1)%n]:
    #        print('Successful key derivation', i)
    #    if SK[i] != SK[(i+1)%n]:
    #        print('Unsucessful key derivation', i)

latency=[]
n=3
for n in range(3,21):
    start=time.time()
    ABCD()
    end=time.time()
    latency.insert(n,end-start)
    n += 1
#print(latency)
n = [str(i) for i in range(3,21)]
#print(n)

def bar_plot():
    plt.bar(n,latency)
    plt.xlabel('No. of Participants in the group')
    plt.ylabel('Latency (s)')
    plt.title('Latency Measurements in ABCD Protocol (p=2048, hash=SHA256)')
    plt.show()
bar_plot()
