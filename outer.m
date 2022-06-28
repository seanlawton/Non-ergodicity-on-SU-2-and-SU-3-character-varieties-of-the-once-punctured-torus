(* ::Package:: *)

(* ::Title:: *)
(*SL(3,\[DoubleStruckCapitalC])-Character Varieties*)


(* ::Subtitle:: *)
(*Written by Sean Lawton in 2005-2006 (partially based on code written by William Goldman for free group computations).*)


(* ::Input::Initialization:: *)
Off[General::"spell1"];Off[General::"spell"];Off[Syntax::"tsntxi"];Off[Solve::"svars"]
DelimiterFlashTime->0;


(* ::Input::Initialization:: *)
$IterationLimit=Infinity;


(* ::Input::Initialization:: *)
Unprotect[Word,Dot,Inverse,Power];
Word[a___,m_Integer,n_Integer,b___] := Word[a,b] /; m + n == 0
Dot[Word[],Word[]] := Word[]
Dot[Word[],Word[a__]] := Word[a]
Dot[Word[a__],Word[]] := Word[a]
Dot[Word[a___],Word[b___]] := Word[a,b]
Power[Word[a___],0]:=Word[]
Power[Word[a___],1]:=Word[a]
Power[Word[a___],i_Integer]:=Word[a] . Power[Word[a],i-1]/;i>0
Power[Word[a___],i_Integer]:=Inverse[Power[Word[a],-i]]/;i<0
Word[a___,0,b___] := Word[a,b]
Inverse[Word[]] := Word[]
Inverse[Word[n_Integer]] := Word[- n]
Inverse[Word[a___,n_Integer]] := Word[- n] . Inverse[Word[a]]

Dot[W__,Word[b__]+Word[c__]]:=Dot[W,Word[b]]+Dot[W,Word[c]];
Dot[Word[a__]+Word[b__],W__]:=Dot[Word[a],W]+Dot[Word[b],W];
Dot[W_,U_+V_]:=Dot[W,U]+Dot[W,V];Dot[U_+V_,W_]:=Dot[U,W]+Dot[V,W];

Protect[Dot,Word,Inverse,Power];


(* ::Input::Initialization:: *)
toList[w_Word] := Apply[List,w];
toWord[l_List] := Apply[Word,l];
ExponentSum[l_List,j_Integer] := Length[Cases[l,j]] - Length[Cases[l,-j]]
HomologyClass[w_Word] := Module[{l=toList[w]},Table[ExponentSum[l,j],{j,2}]]



(* ::Input::Initialization:: *)
TTrace[Word[]] := 3
TTrace[Word[i_Integer,a__,j_Integer]] := TTrace[Word[a]]     /; i+j ==0
TTrace[Word[i_Integer,j_Integer]]:=TTrace[Word[j,i]] /;Abs[j]<Abs[i]
TTrace[Word[i_Integer,j_Integer,k_Integer,l_Integer]]:=TTrace[Word[l,i,j,k]] /;((i-j)*(i-l)!=0 && l+j==0==i+k && (l>0||k>0))
TTrace[Word[i_Integer,a__,j_Integer]]:=TTrace[Word[i,i,a]] /;(i-j==0 &&Word[i]^Length[Word[a]]=!=Word[a])
TTrace[Word[a_Integer,b_Integer,c_Integer,d_Integer]]:=TTrace[Word[a,b]]*TTrace[Word[a,-b]]-TTrace[Word[-a,-b]]*TTrace[Word[-b,-b]]+TTrace[Word[-a,-b,-b,-b]]/;(a-c==0 && b+d==0)
TTrace[Word[b_Integer,c_Integer,d_Integer,a_Integer]]:=TTrace[Word[a,b]]*TTrace[Word[a,-b]]-TTrace[Word[-a,-b]]*TTrace[Word[-b,-b]]+TTrace[Word[-a,-b,-b,-b]]/;(a-c==0 && b+d==0)
TTrace[Word[c___,a__,b__,d___]]:=TTrace[Word[a]]*TTrace[Word[c,a,d]]-TTrace[Inverse[Word[a]]]*TTrace[Word[c,d]]+TTrace[Word[c] . Inverse[Word[a]] . Word[d]]/;Word[a]==Word[b]
TTrace[Word[m___,a__,b__,c__,n___]]:=-TTrace[Word[m,b,a,a,n]]-TTrace[Word[m,a,a,b,n]]+TTrace[Word[a]]*TTrace[Word[m,a,b,n]]+TTrace[Word[a]]*TTrace[Word[m,b,a,n]]+TTrace[Word[b]]*TTrace[Word[m,a,a,n]]-TTrace[Word[a]]*TTrace[Word[b]]*TTrace[Word[m,a,n]]+TTrace[Word[a,b]]*TTrace[Word[m,a,n]]-TTrace[Inverse[Word[a]]]*TTrace[Word[m,b,n]]+TTrace[Inverse[Word[a]]]*TTrace[Word[b]]*TTrace[Word[m,n]]+TTrace[Word[a,a,b]]*TTrace[Word[m,n]]-TTrace[Word[a]]*TTrace[Word[a,b]]*TTrace[Word[m,n]]/;Word[a]==Word[c]
TTrace[Word[a_Integer,b_Integer,c_Integer,d_Integer]]:=-3-TTrace[Word[b,a] . Inverse[Word[a,b]]]+2*TTrace[Inverse[Word[b]]]*TTrace[Word[b]]+TTrace[Word[a]]*TTrace[Inverse[Word[a]]]-TTrace[Inverse[Word[b]]]*TTrace[Inverse[Word[a]]]*TTrace[Word[a,b]]+TTrace[Word[a,b]]*TTrace[Inverse[Word[a]] . Inverse[Word[b]]]-TTrace[Word[a,b] . Inverse[Word[a]] . Word[b]]*TTrace[Word[b]]+TTrace[Inverse[Word[a]]]*TTrace[Word[b]]*TTrace[Word[a,b,b]]+TTrace[Word[a,b,b]]*TTrace[Inverse[Word[a,b,b]]]-TTrace[Word[a,b,b]]*TTrace[Inverse[Word[b,a]]]*TTrace[Inverse[Word[b]]]/;(a+c==0 && b+d==0 && Abs[a]>Abs[b])



(* ::Input::Initialization:: *)
TTrace[n_*w_]:=n*TTrace[w];TTrace[0]:=0;TTrace[Pi*w_]:=Pi*TTrace[w];TTrace[Exp[1]*w_]:=Exp[1]*TTrace[w];
TTrace[w_+u_]:=TTrace[w]+TTrace[u];


(* ::Input::Initialization:: *)
ApplyWord[Word[],l_List] := Word[]
ApplyWord[Word[a_/;a> 0,b___],l_List ] := l[[a]] . ApplyWord [Word[b],l]
ApplyWord[Word[a_/;a<0,b___],l_List] := Inverse[l[[-a]] ] . ApplyWord[Word[b],l]
ApplyAuto[A_,W_Word] := ApplyWord[W,A]
ApplyAuto[A_,i_Integer]:=i
ApplyAuto[A_,r_Rational]:=r
ComposeAuto[A1_,A2_] := Map[ApplyWord[#,A2]&,A1]
ComposeAuto[A1_,A2_,X__] := ComposeAuto[A1,ComposeAuto[A2,X]]
Basis0 = {Word[1],Word[2]};
InnerAutomorphism[w1_Word,w2_Word]  := w1 . w2 . Inverse[w1]
Inn[w_Word] := Map[InnerAutomorphism[w,#]&,Basis0]
Inn[w__] := Inn[Word[w]]
Rep[A_,l_List] := Map[ApplyAuto[A,#]&,l]



(* ::Input::Initialization:: *)
Unprotect[Outer];
Outer[]:={Word[1],Word[2]}
Outer[1]:= {Word[2],Word[1]}
Outer[2]:={Word[-1],Word[2]}
Outer[3]:={Word[1,2],Word[2]}
Outer[i__Integer,j__Integer]:=ComposeAuto[Outer[i],Outer[j]]
Protect[Outer];



(* ::Input::Initialization:: *)
convert[o_List]:=o/.{Outer[]->1,Outer[1]->d[2],Outer[2]->d[3],Outer[3]->N,Outer[1,2]->d[4],Outer[2,1]->d[5],Outer[1,2,1]->d[6],Outer[2,1,2]->d[7],Outer[1,2,1,2]->d[8]}



(* ::Input::Initialization:: *)
TrAutoTerm[A_,P_,p_Integer] := toProduct[Map[TracePoly[#,S]&,Rep[A,fromTrace[unPower[Part[toList[P],p]]]]]]
TrAuto[A_,P_]:=toSum[Table[TrAutoTerm[A,P,i],{i,Length[toList[P]]}]]


(* ::Input::Initialization:: *)
toSum[l_List]:=Apply[Plus,l]
toList[a_t]:={a}
toList[a__t*b__t]:={a*b}
toList[a__t^n_Integer]:={a^n}
toList[a__t*b__t^n_Integer]:={a*b^n}
toList[a__t^n_Integer*b__t]:={a^n*b}
toList[a__t^n_Integer*b__t^m_Integer*c___t]:={a^n*b^m*c}
toList[p_]:=Apply[List,p]
toList[i_Integer]:={i}
toList[i_Integer*a__t]:={i*a}
toList[i_Integer*a__t^n_Integer]:={i*a^n}
toList[i_Integer*a__t*b__t^n_Integer]:={i*a*b^n}
toList[i_Integer*a__t^n_Integer*b__t^m_Integer]:={i*a^n*b^m}
toList[i_Integer*a__t^n_Integer*b__t^m_Integer*c___t]:={i*a^n*b^m*c}
fromTrace[t[i_/;(i>0 &&i<3)]]:=Word[i]
fromTrace[t[i_Integer]]:=Inverse[fromTrace[t[-i]]]/;i<0
fromTrace[t[3]]:=Word[1,2]
fromTrace[t[4]]:=Word[1,-2]
fromTrace[t[5]]:=Word[1,2,-1,-2]
toProduct[l_List]:=Apply[Times,l]
fromTrace[n_Integer]:=n
fromTrace[r_Rational]:=r
fromTrace[l_List]:=Table[fromTrace[Part[l,i]],{i,Length[l]}]


(* ::Input::Initialization:: *)
unPower[a_Integer*b__^m_Integer]:=Join[Table[b,{i,m}],{a}]
unPower[b__^m_Integer]:=Table[b,{i,m}]
unPower[a__*b__]:=Join[unPower[a],unPower[b]]
unPower[a__*b__*c__]:=Join[unPower[a*b],unPower[c]]
unPower[a__*b__*c__]:=Join[unPower[b*c],unPower[a]]
unPower[a__^1]:={a}


(* ::Input::Initialization:: *)
TracePoly[Word[w__],{a_,b_,c_,d_,e_,f_,g_,h_,i_}] := Expand[TTrace[Word[w]]/.{TTrace[Word[1]]->a,TTrace[Word[2]]->b,TTrace[Word[1,2]]->c,TTrace[Word[-1]]->d,TTrace[Word[-2]]->e,TTrace[Word[-1,-2]]->f,TTrace[Word[1,-2]]->g,TTrace[Word[-1,2]]->h,TTrace[Word[1,2,-1,-2]]->i}]
TracePoly[Word[],s_List]:=3
TracePoly[i_Integer,l_List]:=i
TracePoly[r_Rational,l_List]:=r
TracePoly[l_List,s_List]:=Table[TracePoly[Part[l,i],s],{i,Length[l]}]
S={t[1],t[2],t[3],t[-1],t[-2],t[-3],t[4],t[-4],t[5]};


(* ::Input::Initialization:: *)
c[p_,i_Integer]:=Coefficient[p,t[5],i]


(* ::Input::Initialization:: *)
DSym[P_,c_,d_]:=Expand[c*(TrAuto[Outer[],P]+TrAuto[Outer[1],P]+TrAuto[Outer[2],P]+TrAuto[Outer[1,2],P]+TrAuto[Outer[2,1],P]+TrAuto[Outer[1,2,1],P]+TrAuto[Outer[2,1,2],P]+TrAuto[Outer[1,2,1,2],P])+d]



(* ::Input::Initialization:: *)
p=t[1]t[-1]t[2]t[-2]-4t[1]t[-2]t[-4]+2t[-1]t[1]+2t[3]t[-3];



(* ::Input::Initialization:: *)
q=2t[1]^2t[-1]^2t[2]t[-2]+4t[1]^2t[2]^2t[3]-4t[1]^3t[2]t[-2]-8t[1]^2t[-1]t[-2]t[-4]-4t[1]t[2]t[-2]t[3]t[4]+8t[1]t[3]t[-4]^2+8t[1]t[2]^2t[-4]-8t[1]t[2]t[3]^2+4t[2]^2t[-3]t[4]+t[1]t[-1]t[2]t[-2]+t[3]t[-3]t[4]t[-4]+4t[1]t[-1]t[3]t[-3]+4t[1]^3+4t[3]^3+12t[1]t[-2]t[-4]-12t[2]t[3]t[-4]-12t[1]t[-1]-12t[3]t[-3];


(* ::Input::Initialization:: *)
P=DSym[p,1/8,-3];


(* ::Input::Initialization:: *)
Q=DSym[q,1/8,9];


(* ::Input::Initialization:: *)
M[Word[u__], Word[v__]]:=Expand[3*TTrace[Word[u] . Word[v]]-TTrace[Word[u]]*TTrace[Word[v]]/.{TTrace[Word[1]]->t[1],TTrace[Word[2]]->t[2],TTrace[Word[1,2]]->t[3],TTrace[Word[-1]]->t[-1],TTrace[Word[-2]]->t[-2],TTrace[Word[-1,-2]]->t[-3],TTrace[Word[1,-2]]->t[4],TTrace[Word[-1,2]]->t[-4],TTrace[Word[1,2,-1,-2]]->t[5]}]
