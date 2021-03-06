

InstallMethod( OneMutable,true,[IsCcElement],0,c -> One(InCcGroup(c)) );
#R1^(-1)*(I*(C1*x))

ComplementIntMatWithTransforms:=function( full,sub )
local F, S, M, r, T, c, R;
  F := BaseIntMat( full );
  if IsEmpty( sub ) or IsZero( sub ) then
  return rec( complement := F, sub := [], moduli := [] );
  fi;
  S := BaseIntersectionIntMats( F, sub );
  if S <> BaseIntMat( sub ) then
    Error( "sub must be submodule of full" );
  fi;
  # find T such that BaseIntMat(T*F) = S
  M := Concatenation( F, S );
  T := NormalFormIntMat( M, 4 ).rowtrans^-1;
  T := T{[Length(F)+1..Length(T)]}{[1..Length(F)]};
  c := NormalFormIntMat(T*F,6)!.rowtrans;

  # r.rowtrans * T * F = r.normal * r.coltrans^-1 * F
  r := NormalFormIntMat( T, 13 );
  M := r.coltrans^-1 * F;
  R := rec( complement := BaseIntMat( M{[1+r.rank..Length(M)]} ),
            sub := r.rowtrans * T * F,
            moduli := List( [1..r.rank], i -> r.normal[i][i] ) ,
	    fulltrans := r.coltrans^(-1),
	    subtrans := r!.rowtrans*c^(-1));
  return R;
end;



#& cohomology #&

UniversalCoefficientsTheorem:=function(K,n)
local ZZ,     # a basis for Z_n(K)
      B,      # a basis for B_n(K)
      r,      # the ABT for Z_n(K) and B_n(K)
      C,      # the matrix C
      D,      # the list of the invariant factors
      m,      # the exponent of the H_n(K)
      homlist,# a "basis" for Hom(H_n(K),Z/mZ)
      r2, R1,C1,
              # the different variables implicated
              # in the ABT for K_n and Z_n(K)		
      I,      # the matrix I
      cocyclelist,
              # a "basis" for H^n(K,C^*)
	BB, i , hom ;

ZZ:=NullspaceIntMat(TransposedMat(
                BoundaryMatrix(K,n)));
if not Size(ZZ)>0 then return 
	rec(	complex:=K,
		cyclebasis:=ZZ,
		cycletrans:=[],
		hombasis := [],
		cocyclebasis := [],
		torsion := [1],
		exponent := 1,
		lift:=[],
		 moduli:=[],
	r:=[],
	c:=[],
	id:=[]
	);
fi;
B:=BaseIntMat(TransposedMat(
                 BoundaryMatrix(K,n+1)));
r:=ComplementIntMatWithTransforms(ZZ,B);
BB:=r!.sub;
C:=r!.fulltrans;
D:=r!.moduli;
m:=D[Size(D)];
homlist:=[];
List(Filtered(D,x->not x=1),x->
	ListWithIdenticalEntries(Size(ZZ),0));
for i in [1..Size(D)] do
	if D[i]=1 then continue;fi;
	hom:=ListWithIdenticalEntries(Size(ZZ),0);
	hom[i]:=m/D[i];
	Add(homlist,hom);
od;
homlist:=List(homlist,x->((C^(-1))*x) mod m);

r2:=ComplementIntMatWithTransforms(
              IdentityMat(K!.dimension(n)),ZZ);
C1:=r2!.subtrans;
R1:=r2!.fulltrans;

I:=Concatenation(IdentityMat(Size(ZZ)),
     NullMat(K!.dimension(n)-Size(ZZ),Size(ZZ)));
cocyclelist:=List(homlist,x->(R1^(-1)*(I*(C1*x))) mod m);

return( rec(
	complex:=K,
	boundarybasis:=BB,
	cyclebasis:=ZZ,
	cycletrans:=C,
	hombasis := homlist,
	cocyclebasis := cocyclelist,
	torsion := Filtered(D,x->not x=1),
	exponent := m,
	lift:=R1^(-1)*I*C1,
	moduli:=D)
	);
end;

#& end #&


#& order #&

CocycleOrder:=function(f,m)
	local list;
	list:=List(Filtered(f,x->not x=0),
                   x->m/Gcd(x,m));
	if list=[] 
		then return 1;
		else return Maximum(list);
	fi;
end;    

#& end #&   

#& functoriality #&

GroupCohomologyFunctor:=function(K1,K2,phi,n)
local 	UCT1, 	# UCT for K1
	m1, 	# the exponent of H_n(K1)
	Z1,	# the adapted basis of Z_n(K1)
	UCT2, 	# UCT for K2
	m2, 	# the exponent of H_n(K2)
	Z2,	# the adapted basis of Z_n(K2)
	p, 	# p=lcm(m1,m2)
	F, 	# the matrix F
	hphi,   # the morphism H_n(phi)
	s; 	


UCT1:=UniversalCoefficientsTheorem(K1,n);;
m1:=UCT1!.exponent;;
Z1:=UCT1!.cyclebasis;
s:=NormalFormIntMat(Z1,13);
UCT2:=UniversalCoefficientsTheorem(K2,n);;
m2:=UCT2!.exponent;;
Z2:=UCT2!.cyclebasis;
F:=List(Z1, x->SolutionIntMat(Z2,phi!.mapping(x,n)));;
p:=Lcm(m1,m2);;

hphi:=function(f)
	return ((F*(m1*f))/m2) mod m1;
end;
return rec(
	matrix:=F,
	mapping:=hphi,
	p:=p,
	m1:=m1,
	m2:=m2);
end;

#& end #&


#& proj #&

ProjectiveCharacters:=function(G,alpha,o)
    local A,r,Ga,Gaa,ire,t,lift,testpro, cocvals;
    
cocvals:=function(alpha,G) local x,y; for x in G do for y in G do Print(alpha(x,y),",");od;od;end;
# we represent the cyclic group as a G-Outer group

A:=GOuterGroup();
SetActingGroup(A,G);
if o=1 then
    SetActedGroup(A,GroupByGenerators(
	[One(CyclicGroup(o))]));
    else
        SetActedGroup(A,CyclicGroup(o));
fi;
SetOuterAction(A,function(g,x) return x; end);

# we represent the cocycle f as a 
# standard 2-cocycle in HAP 

r:=Standard2Cocycle();
SetActingGroup(r,A!.ActingGroup);
SetMapping(r,function(x,y) return 
	(A!.ActedGroup.1)^(alpha(x,y));
	end);
SetModule(r,A);


# now, we construct the extension of G by A along r
# we also give its character table

Ga:=CcGroup(A,r);
Gaa:=UnderlyingGroup(Ga);

ire:=Irr(Gaa);

# we give the element in Gaa that corresponds to 
# the generators of the cyclic group, and a
# section of the epi of Gaa on G


t:=CcElement(FamilyObj(One(Ga)),GeneratorsOfGroup(
   Ga!.Fibre)[1],One(Ga!.Base),InCcGroup(One(Ga)));
lift:=function(g)
      return CcElement(FamilyObj(One(Ga)),
	One(Ga!.Fibre),g,InCcGroup(One(Ga)));
end;

# finally, we give the function that tests for a
# charater of Gaa if it comes from a projective
# character of G

testpro:=function(l)
	local list,chi;
	list:=[];
	for chi in l do
      		if t^chi/E(o)=(t^Size(Ga))^chi 
			then Add(list,chi); 
		fi;
	od;
	return list;
end;

return rec(
	Gaa:=Gaa,
	lift:=lift,
	table:=testpro(ire)
	);
end;

#& end #&










#& end #&




alphag:=function(g)
#local f,x,y;
return function(f)
	return function(x,y)
    		return f(x,y,g);end;
	end;
end;

#& indicator #&


#& end #&


#& adaptation #&

coboundary:=function(eta)
return
  function(g,h,k) 
   return eta(h,k)-eta(g*h,k)+eta(g,h*k)-eta(g,h);
  end;
end;

moduloQ:=function(G,H,Q,g)
local p;
for p in Q do
 if p^-1*g in H then return [p,p^(-1)*g]; fi;
od;
end;

FirstStep:=function(G,H,Q,omega)
local eta_1,omega_0;
eta_1:=function(g,h)
 return omega(moduloQ(G,H,Q,g)[1],
         moduloQ(G,H,Q,g)[2],moduloQ(G,H,Q,h)[2]);
end;
omega_0:=function(g,h,k) 
 return omega(g,h,k) +coboundary(eta_1)(g,h,k); 
end;
return omega_0;
end;

SecondStep:=function(G,H,Q, omega_0)
local eta_2,omega_1;
eta_2:=function(g,h) 
 return 
  -(omega_0(g,moduloQ(G,H,Q,h)[1],
            moduloQ(G,H,Q,h)[2]))
  +omega_0(moduloQ(G,H,Q,g)[1],moduloQ(G,H,Q,g)[2],
   moduloQ(G,H,Q,h)[1]);
 end;
omega_1:=function(g,h,k) 
 return omega_0(g,h,k)+coboundary(eta_2)(g,h,k);
end;
return omega_1;
end;

ThirdStep:= function (G, N, Q, omega_1)
local  eta_3, omega_2;
eta_3 := function (g,h)
	return omega_1(moduloQ(G,N,Q,g)[1], moduloQ(G,N,Q,g)[2], h);
	end;
omega_2 := function (g, h, k)
	return omega_1(g, h, k) + coboundary(eta_3)(g, h, k);
	
end;
return omega_2;
end;



AdaptedCocycle1 := function(G, R, H, omega)
local omega1, omega2, omega3, Q;
Q:=List(RightCosetsNC(G,H),x->Representative(x)^-1);
omega1:=FirstStep(G, H, Q, omega);
omega2:=SecondStep(G, H, Q, omega1);
return omega2;
end;

IsAdaptedCocycle:=function(G,N, omega, exp)
    local g,h,k,bool;
    for g in G do
        for h in G do
            for k in N do
                if not (omega(g,h,k) mod exp = 0) then return omega(g, h, k); 
                fi;
            od;
        od;
    od;
    return true;
end;





#& end #&








act:=function(h,f) #takes two arguments, a subgroup h and an automorphism f, returns f(h)
if Size(GeneratorsOfGroup(h))=0 then return h;
else
return (Group(List(GeneratorsOfGroup(h), x->x^f)));
fi;
end;


IsDirectFactor:= function (h, factors)
local flag, AllFactors, Groups, GroupSizes, ctr, poslist, CheckList;
flag:=false;
AllFactors:=Combinations(factors);
Remove(AllFactors,1);
Groups:= List(AllFactors, DirectProduct);
GroupSizes:= List(Groups, Size);
if not Size(h) in GroupSizes then flag:=false;
else 	ctr:=1;
	poslist:= Positions (GroupSizes, Size(h));
	CheckList:= Groups{poslist};
	while flag=false and ctr <= Size(CheckList) do
		if not IsomorphismGroups(CheckList[ctr], h)= fail then flag:= true;fi;
		ctr := ctr+1;
	od;
 fi;
return flag;
end;

IsAbelianDirectFactor:= function (x, fact)
local flag;
flag:=false;
if IsAbelian (x) then if IsDirectFactor (x, fact) then flag:=true;fi;fi;
return flag;
end;

SubgroupsUptoAutomorphism:= function (g)
local AutomorphismOrbits, OrbitsReps, DF, SubgroupList;
AutomorphismOrbits:= Orbits(AutomorphismGroup(g), AllSubgroups(g),act);
OrbitsReps := Filtered( List( AutomorphismOrbits, function ( x )
              return x[1];
          end ), function ( x )
            return not Size( x ) = 1 and not Size( x ) = Size( g );
        end );
return OrbitsReps;
end;



#& subgroup complex &#

SubgroupComplex:= function (G,R, i)
    local ResR, f, liftf, ResK, F;
    
    ResR:= ResolutionFiniteGroup(i,4);
f:=GroupHomomorphismByImagesNC(i, G, GeneratorsOfGroup(i), GeneratorsOfGroup(i));
liftf:=EquivariantChainMap(ResR, R, f);
ResK:=TensorWithIntegers(ResR);
F:=TensorWithIntegers(liftf);
return  rec (subgroup:= i, complex:= ResK, chainmap:=F, Rchainmap:= liftf, resolution:= ResR);
end;



SubgroupComplexes := function (G, R)
local Subgroups, SubRes, h, ResR, f, liftf, ResK, F;
Subgroups:=SubgroupsUptoAutomorphism(G);
SubRes:=[];
return (List(Subgroups, x-> SubgroupComplex(G, R, x)));
end;

#& end &#


rcv:=function(x,exp) 
     return List(x,y->ZmodnZObj(y,exp));
     end;

StabHOrbitsCocycles:=function(G,R,K,UCT, comp, n)
local 	H, 
	KH, 
	f, 
	M, 
	rcv, 
	modhom, 
	ker, 
	coho,
	aut,
	gens,
	autmat,
	orbits, 
	OrbitList;
H:=comp!.subgroup;
KH:=comp!.complex;
f:= comp!.chainmap;
M:=GroupCohomologyFunctor(KH, K, f, n)!.matrix;


rcv:=function(x,exp) 
     return List(x,y->ZmodnZObj(y,exp));
     end;
modhom:=List(UCT!.hombasis, x->rcv(x,UCT!.exponent));
coho:=NearAdditiveGroup(modhom);

aut:=Stabilizer(AutomorphismGroup(G), H, act);
gens:=GeneratorsOfGroup(aut);
autmat:=List(
         gens,phi->TransposedMat(
          GroupCohomologyFunctor(
           K,K,TensorWithIntegers(
	    EquivariantChainMap(R,R,phi)),
           n)!.matrix));
autmat:=List(
         autmat,x->List(
                    x,y->rcv(y,UCT!.exponent)));
                  
orbits:=OrbitsDomain(aut,coho,gens,autmat);
#Print(orbits);
OrbitList:= List(orbits,x->List(x,y->List(
                                 y,z->Int(z))));
return OrbitList; 
end;

#& cochains &#


CohomologyList:= function (G, R, K, UCT, res, cocycles, n)
local m, cocycleList, jj, restr;
m:=UCT!.exponent;
cocycleList:=[];
for jj in cocycles do
    restr:=GroupCohomologyFunctor(res!.complex,K,res!.chainmap, n)!.mapping(jj);
    if Set(restr)=[0] then Add(cocycleList, jj); fi;# check if the elements are all 0, if not  add to list
   od;
   return cocycleList;
end;
  


CoboundaryList:= function(UCT, comp, cohlist, n)
local m,idmat,mapmat,cocyclelift,coboundarylist;
m:=UCT!.exponent;
   idmat:=IdentityMat(comp!.complex!.dimension(3));
   mapmat := List(idmat, r-> comp!.chainmap!.mapping(r, 3));
   cocyclelift:= List(cohlist, coh -> (UCT!.lift*coh) mod m);
   coboundarylist:=List(cocyclelift, x-> x*TransposedMat(mapmat) mod m);
return coboundarylist;
end;

RemoveLast := function (x , n )
local i;
for i in [1.. n ] do
Remove ( x );
od ;
return x ;
end ;

	CochainList:= function (subres, coblist, m, n) 
	local   mp,
		coboundarysize,
		scalarmat, concatmat, w,
		boundarymat, homology, vectlist;
	if coblist=[] then return [];fi;
	if Set(coblist) = [0] then return ListWithIdenticalEntries( subres!.complex!.dimension(n-1), 0);fi;
	homology:=Homology(subres!.complex, n-1);
	if not homology=[] then
	mp:=Lcm(homology); else mp := 1;fi;
	coboundarysize:= Size(coblist[1]);
	boundarymat:=BoundaryMatrix(subres!.complex, n);
	scalarmat:=m*mp*IdentityMat(coboundarysize);
	concatmat:= Concatenation(boundarymat, scalarmat); 
	w:= List (coblist, cob -> SolutionIntMat(concatmat, mp*cob));
	vectlist:= List (w, x -> RemoveLast(x, coboundarysize));
	return vectlist mod (m*mp);
	end;






	

CocycleValues:=function ( lstG, f, exp )
    local posG, g, h, k, valuesh, valuesk, cocyclevalues;
    cocyclevalues:=[];
    for g in lstG do
        valuesh := [  ];
        for h in lstG do
            valuesk := [  ];
            for k in lstG do
                Add( valuesk, f( g, h, k ) mod exp );
            od;
            Add( valuesh, valuesk );
        od;
        Add( cocyclevalues, valuesh );
    od;
    return cocyclevalues;
        end;



Alpha_symb:=function(G,w,g)
 local listG,posG;
 listG:=EnumeratorSorted(G);
 posG:=function(g)
  return Position(listG,g);
 end;
 if IsDenseList(w) 
 then
  return function( arg )
   local x,y;
   x:=posG(arg[1]);
   y:=posG(arg[2]);
   return w[x][y][posG(g)];
  end;
 else
  return function ( arg )
   local x,y;
   x:=arg[1];
   y:=arg[2];
   return w(x,y,g);
  end;
 fi;
end;



CosetStab:= function (h, elt)
local Im; # for an element elt, gives Stabilizer of elt*H in H
	Im:=Image(ConjugatorIsomorphism (h, elt^-1));
	return Intersection (Im, h);	
end;	
		
		
SimplesGenerator := function(g, R, K, h, omega, exp, n ) #generates simples for C(g,h , 1, 1) for g a group and h a subgroup of g
    local DC, DCSize, RCRepList, DCReps, Stab, dcrep, quot, x, rcreps, i,j, r,s, Irreps, Simples, reps, flag, temp;
    
    

	DC:=DoubleCosetsNC(g, h, h); #computes double cosets H\G/H
DCSize:=Size(DC); #number of double cosets


DCReps:= DoubleCosetRepsAndSizes(g,h,h);

RCRepList:=[]; 
for i in [1..DCSize] do
	dcrep:=DCReps[i][1];
	quot:=RightCosetsNC(h, CosetStab(h, dcrep));
	rcreps:=[];
	for j in [1.. Size(quot)] do
		Add(rcreps, Representative(quot[j])^-1*dcrep);
	od;
Add(RCRepList, rcreps);
od;
Simples:=[];

for r in [1..DCSize] do
	x:= DCReps[r][1];
	Stab := CosetStab (h, x);
	Irreps:= ProjectiveCharacters(Stab,alphag(x)(omega), exp);
        if x = One(g) then
            flag:=1;
            reps:= List(ConjugacyClasses(Stab), Representative);
            for i in [1..Size(Irreps.table)] do if Set( List(reps, y-> Irreps!.lift(y)^Irreps!.table[i]))=[1] then flag:=i;fi;od;
            if not flag=1 then 
                temp:=Irreps!.table[flag];
                Irreps!.table[flag]:=Irreps!.table[1];
                Irreps!.table[1]:=temp;
            fi;
        fi;
        
	for s in [1..Size(Irreps!.table)] do
            
		Add(Simples, rec( dim:=(Irreps!.lift(One(Stab))^Irreps!.table[s])*Index(h, Stab), dcoset:= DC[r], rcreps:= RCRepList[r], irrep:= Irreps!.table[s], stab:= Stab, lift:=Irreps!.lift)); #creates list of simples
	od;
od;
return rec(simples:=Simples, rcreplist:=RCRepList);
end;


SimplesGenerator2 := function(g, R, K, h, omega, exp, n ) #generates simples for C(g,h , 1, 1) for g a group and h a subgroup of g
    local DC, DCSize, RCRepList, DCReps, Stab, dcrep, quot, x, rcreps, i,j, r,s, Irreps, Simples, reps, flag, temp;

	DC:=DoubleCosetsNC(g, h, h); #computes double cosets H\G/H
DCSize:=Size(DC); #number of double cosets


DCReps:= DoubleCosetRepsAndSizes(g,h,h);

RCRepList:=[]; 
for i in [1..DCSize] do
	dcrep:=DCReps[i][1]*h.1;
	quot:=RightCosetsNC(h, CosetStab(h, dcrep));
	rcreps:=[];
	for j in [1.. Size(quot)] do
		Add(rcreps, Representative(quot[j])^-1*dcrep);
	od;
Add(RCRepList, rcreps);
od;
Simples:=[];
for r in [1..DCSize] do
	x:= DCReps[r][1];
	Stab := CosetStab (h, x);
	Irreps:= ProjectiveCharacters(Stab,alphag(x)(omega), exp);
        if x = One(g) then
            flag:=1;
            reps:= List(ConjugacyClasses(Stab), Representative);
            for i in [1..Size(Irreps.table)] do if Set( List(reps, y-> Irreps!.lift(y)^Irreps!.table[i]))=[1] then flag:=i;fi;od;
            if not flag=1 then 
                temp:=Irreps!.table[flag];
                Irreps!.table[flag]:=Irreps!.table[1];
                Irreps!.table[1]:=temp;
            fi;
        fi;
        
	for s in [1..Size(Irreps!.table)] do
            
		Add(Simples, rec( dim:=(Irreps!.lift(One(Stab))^Irreps!.table[s])*Index(h, Stab), dcoset:= DC[r], rcreps:= RCRepList[r], irrep:= Irreps!.table[s], stab:= Stab, lift:=Irreps!.lift)); #creates list of simples
	od;
od;
return rec(simples:=Simples, rcreplist:=RCRepList);
end;



char:= function (simple, cocyclev,lstG, H, z, s, exp) # gives the character of a couple (z,s) where z, s in G
    local flag, d, rcrep, x, l, chi, h, posG;
    posG:=function(g) return Position(lstG, g);
          end;
flag:=0;
l:=simple!.lift;
chi:= simple!.irrep;
 d := simple!.rcreps[1];
if z in simple!.dcoset and s in CosetStab(H, z) then 
	for rcrep in simple!.rcreps do
		if rcrep^-1*z in H then x:= rcrep; break; fi;
		od;
		h:=x*d^-1;
		return E(exp)^(-cocyclev[posG(h)][posG(h^-1*s*h)][posG(d)] + cocyclev[posG(s)][posG(h)][posG(d)])*(l(h^-1*s*h))^chi; 
else return 0;fi;
end;


tensorchar := function (simple1, simple2, g,  s, H, cocyclev, lstG,  exp)
local charvalue, a, posG;
     posG:=function(g) return Position(lstG, g);
          end;
    charvalue:= 0;
for a in simple1!.rcreps do
	if s in CosetStab(H, a) then
	charvalue := charvalue + E(exp)^(+ cocyclev[posG(a)][posG(a^-1*s*a)][posG(a^-1*g)] - cocyclev[posG(s)][posG(a)][posG(a^-1*g)])*char(simple1, cocyclev, lstG,  H, a, s, exp)*char(simple2, cocyclev, lstG, H, a^-1*g, a^-1*s*a, exp);fi;
od;
return charvalue;
end;
#

multiplicity:= function (no1, no2, no3, Simples, H, omega, lstG, exp)
local simple1, simple2, sim, mult, vect, dcrep, stabgrp, h;
simple1:=Simples!.simples[no1];
simple2:=Simples!.simples[no2];
sim:=Simples!.simples[no3];
mult:=0;
vect:=[];
dcrep:=sim!.rcreps[1];
	stabgrp:=sim!.stab;
		for h in stabgrp do
			mult := mult + tensorchar(simple1, simple2, dcrep, h, H, omega, lstG,  exp)*ComplexConjugate(sim!.lift(h)^sim!.irrep);
		od;
return mult/Size(stabgrp);
end;



dsd := function (no1, no2, Simples, H, omega, lstG, exp)
local totalvect, item, decomp;
totalvect:=[];
for item in [1..Size(Simples!.simples)] do
	decomp:=multiplicity(no1, no2, item, Simples, H, omega, lstG, exp);
 	Add(totalvect, decomp); 
 	od;
return totalvect;
end;

FusionRules:= function (Simples, H, adapted, lstG, exp)
local i, j, FusionRing, decomp;
FusionRing:=[];
for i in [1..Size(Simples!.simples)] do
	decomp:=[];
	for j in [1..Size(Simples!.simples)] do
		Add(decomp, dsd(i, j, Simples, H, adapted, lstG,  exp)); 
		od;
		Add(FusionRing, decomp);
	od;
return FusionRing;
end;

SubgroupHomotopy:=function ( RG, RH, chainmap, word )
    local n,f,Elts, Mult, g, lambda, ContractingHomotopy, firstterm, SubHom, secondterm;
    n := Length( word );
    f:=function(x) return Syzygy (RG, x); end;
     Elts := function ( x ) return Position( RG!.elts, x ); end;
Mult := function ( x, w ) return List( w, function ( y )
                  return [ y[1], Position( RG!.elts, x * RG!.elts[y[2]] ) ];
              end );
      end;
	g:=function (x) return chainmap!.mapping(Syzygy(RH,x), n);end;
	lambda:=function (x) return AddFreeWords( f(x), NegateWord( g(x))); end;
	ContractingHomotopy:= function (R, w) local arr, x;arr:=[]; for x in w do arr:= AddFreeWords(arr, R!.homotopy(n,x)); od;return arr; end;

   if n < 1 or n > 2 then
       Print( 
         "ERROR: SubgroupHomotopy() is so far only implemented for 1- and 2- homotopies\
. \n" );fi;
	if n = 1 then
	       return ContractingHomotopy(RG, lambda(word));fi;
       if n = 2 then
       	 firstterm:=ContractingHomotopy(RG, lambda(word));
       	  SubHom := SubgroupHomotopy( RG, RH, chainmap, [ word[1] ] );	
        	SubHom := AddFreeWords( SubHom, Mult( word[1], SubgroupHomotopy( RG,RH, chainmap, [ word[2] ] ) ) );
        	SubHom := AddFreeWords( SubHom, NegateWord( SubgroupHomotopy( RG, RH, chainmap, [ word[1] * word[2] ] ) ) );
		secondterm:=ContractingHomotopy(RG, SubHom);
		return AddFreeWords (firstterm, NegateWord(secondterm)); 
	fi;
end;

HomotopyStandardCocycle:=function (RG, RH, chainmap, f, n, q)
local Standard;
    Standard := function ( arg... )
          local S, v, x, g, h, lst;
          g := arg[1];
          lst := [ g ];
          if Length( arg ) > 1 then
              h := arg[2];
              lst := [ g, h ];
          fi;
          S := SubgroupHomotopy( RG, RH, chainmap, lst );
          Apply( S, function ( x )
                return x[1];
            end );
		  v := ListWithIdenticalEntries( RG!.dimension( n+1 ) , 0);
          for x in S do
              v[AbsoluteValue( x )] := v[AbsoluteValue( x )] + SignInt( x );
          od;
              return v * f mod q;
          return;
      end;
    return Standard;
end;

GHCoho :=function (G, H)
local RG, KG, UCTG, RH, f, liftf, KH, F, comp, allcoho, coho;
RG:=ResolutionFiniteGroup(G, 4);
KG:=TensorWithIntegers(RG);
UCTG:=UniversalCoefficientsTheorem(KG, 3);
RH:= ResolutionFiniteGroup(H, 4);
f:=GroupHomomorphismByImagesNC(H, G, GeneratorsOfGroup(H), GeneratorsOfGroup(H));
liftf:=EquivariantChainMap(RH, RG, f);
KH:=TensorWithIntegers(RH);
F:=TensorWithIntegers(liftf);
comp:= rec (subgroup:= H, complex:= KH, chainmap:=F, Rchainmap:=liftf);
allcoho:=List(StabHOrbitsCocycles(G, RG, KG, UCTG, comp, 3),  x-> x[1]);
coho:= CohomologyList(G, RG, KG, UCTG, comp, allcoho, 3);
return coho;
end;


ValuesOfPiSymbols:=function(G,x,n,f)
local e,o, list1, list2,m,  j;
e:=Exponent(G);
o:=Order(x);
list1:=[1];
for m in [1..o] do
	Add(list1,list1[Size(list1)]*E(n)^f(x,x^(m-1),x));
od;
list2:=[1];
for j in [1..e] do
    Add(list2, list1[o+1]^QuoInt(j, o)*(list1[RemInt(j, o)+1]));
od;
return list2;
end;

nu:=function(G, simple, H, f, exp, m)
    local S, lift, chi, rep, listG, pivalues, sum, r, o;
    
    S:=simple!.stab;
    lift:=simple!.lift;
    chi:=simple!.irrep;
    rep:=simple!.rcreps[1];
    listG:=EnumeratorSorted(G);
    pivalues:=List(listG, x -> ValuesOfPiSymbols(G, x, exp, f));
    sum:=0;
    for r in H do 
        if (rep*r)^m in S then 
            o:=Order(rep*r);
            sum:=sum + (pivalues[Position(listG, rep*r)][o+1]^(QuoInt(-m, o)-1))*pivalues[Position(listG, rep*r)][o+RemInt(-m, o)+1]*(lift((rep*r)^(-m))^chi);
        fi;
    od;
    return sum/Size(S);
end;

FSIforAGT:=function (G, Simples, H, f, exp, FSExp)
    local x, m, result, list;
    result:=[];
    for x in Simples do
        list:=[];
        for m in [0..FSExp-1] do
            Add(list, nu(G,x, H, f, exp, m));
        od;
        Add(result, list);
    od;
    return result;
end;

ExponentOfPFC:=function(G,R,K,UCT,hom)
  local 	H,  
		R2,
		K2,
		UCT2,
		m,
		phi,
		chainmap,
		res,
		list;

list:=[];
for H in Filtered(AllSubgroups(G),
		IsCyclic and IsNonTrivial) do
	R2:=ResolutionFiniteGroup(H,4);
	K2:=TensorWithIntegers(R2);
	UCT2:=UniversalCoefficientsTheorem(K2,3);
	m:=UCT2!.exponent;
	phi:=GroupHomomorphismByFunction(H,G,h->h);
	chainmap:=TensorWithIntegers(
		EquivariantChainMap(R2,R,phi));
	res:=GroupCohomologyFunctor(
		K2,K,chainmap,3)!.mapping(
			hom);
	Add(list,[Size(H),CocycleOrder(res,m)]);
od;
return Lcm(List(list,x->x[1]*x[2]));
end;

newfusion :=function (arg...)
local G,  R, K, UCT, exponent, fring,g, h, k,  subcomp, comp, cocycletest, H, allcoho, coho, coblist, i, f, adapted, Simples, filename, cochlist, UCTH, j ,mu, diff, nontrivindex, newmu, htpystdcocycle, extendedhtpystdcocycle, sc, cobnewmu, cobht, cocyclefn, expH, homology, modhom, hcohomod, hcoho, hcocycles, Hcocyclefnlist, x, extendedx, cobx, dimlist, listG, adaptedv, fsi, fsexp;
G:=arg[1];
listG:=EnumeratorSorted(G);
R:=ResolutionFiniteGroup(G, 4);
K:=TensorWithIntegers(R);
UCT:=UniversalCoefficientsTheorem(K, 3);
exponent:=UCT!.exponent;
if Size(arg)>1 then subcomp:=[SubgroupComplex(G, R, arg[2])]; else subcomp:=SubgroupComplexes(G, R);fi;
for comp in subcomp do
    H:=comp!.subgroup;
    if Size(arg)>2 then coho:=[arg[3]];
        else
    	allcoho := List(StabHOrbitsCocycles(G, R, K, UCT, comp, 3), x-> x[1]);
    coho:= CohomologyList(G, R, K, UCT, comp, allcoho, 3);
    fi;
    coblist:= CoboundaryList(UCT, comp, coho, 3);
	nontrivindex:=[];
        UCTH:=UniversalCoefficientsTheorem(comp!.complex, 2);
        expH:=UCTH!.exponent;
        if UCTH!.hombasis=[] then hcocycles:= [];
            else
	modhom:=List(UCTH!.hombasis, x->rcv(x,expH));
	hcohomod:=NearAdditiveGroup(modhom);
	hcoho:=List(hcohomod, x -> List(x, y -> Int(y)));
	hcocycles:=List(hcoho, x-> exponent*(UCTH!.lift*x));
        Hcocyclefnlist:= List(hcocycles, x-> StandardCocycle(comp!.resolution, x, 2, exponent*expH));fi;
        for i in [1..Size(coho)] do if not Set(coblist[i])=[0] then Add(nontrivindex, i); else
	htpystdcocycle:= HomotopyStandardCocycle(R, comp!.resolution, comp!.Rchainmap, expH*(UCT!.lift*coho[i]) mod (expH*exponent), 2, expH*exponent);
		extendedhtpystdcocycle:= function (g, h) if not g in H or not h in H then return 0; else return htpystdcocycle(g, h);fi;end;
		sc:=StandardCocycle(R, expH*(UCT!.lift*coho[i]) mod (expH*exponent), 3, expH*exponent);
		cobht:=coboundary (extendedhtpystdcocycle);
                if hcocycles=[] then    	
          	    cocyclefn:= function (g,h,k) return sc(g, h, k) - cobht(g, h, k);end;
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		#  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
	#	Print(cocycletest);
	#	Print("\n");
		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
                fsexp:=ExponentOfPFC(G, R, K, UCT, coho[i]);
                fsi:=FSIforAGT(G, Simples!.simples, H, adapted, expH*exponent, fsexp);
	        dimlist:= List(Simples!.simples, x-> x!.dim);
            
                adaptedv:=CocycleValues(listG, adapted, exponent*expH);
		fring:=FusionRules(Simples, H, adaptedv,listG, exponent*expH);
	        filename:= [IdGroup(G), IdGroup(H),coho[i],[] ];
		Print([filename, fring, dimlist, fsi], ",\n");
                    else for x in [1..Size(Hcocyclefnlist)] do
                extendedx:= function (g, h) if not g in H or not h in H then return 0;
                                                else return Hcocyclefnlist[x](g, h);fi;
                                                   end;
                    cobx:=coboundary(extendedx);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k)  - cobx(g, h, k) - cobht(g, h, k);end; 
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
		Print(cocycletest);
		Print("\n");
		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
                fsexp:=ExponentOfPFC(G, R, K, UCT, coho[i]);
                fsi:=FSIforAGT(G, Simples!.simples, H, adapted, expH*exponent, fsexp);
                dimlist:= List(Simples!.simples, x-> x!.dim);
	        adaptedv:=CocycleValues(listG, adapted, exponent*expH); 
	        fring:=FusionRules(Simples, H, adaptedv, listG, exponent*expH);
                filename:= [IdGroup(G), IdGroup(H),coho[i], hcoho[x]];
                Print([filename, fring, dimlist, fsi], ",\n");
	        od;
                fi;fi;
                                       od;
	if not nontrivindex =[] then
	cochlist:=CochainList(comp, coblist, exponent, 3);
        for j in nontrivindex do
        mu := StandardCocycle(comp!.resolution, cochlist[j], 2, exponent*expH);
	newmu := function (g, h) if not g in H or not h in H then return 0; else 
		return mu(g,h); fi; end;
		htpystdcocycle:= HomotopyStandardCocycle(R, comp!.resolution, comp!.Rchainmap, expH*(UCT!.lift*coho[j]) mod (expH*exponent), 2, expH*exponent);
		extendedhtpystdcocycle:= function (g, h) if not g in H or not h in H then return 0; else return htpystdcocycle(g, h);fi;end;
		sc:=StandardCocycle(R, expH*(UCT!.lift*coho[j]) mod (exponent*expH), 3, exponent*expH);
		cobnewmu:= coboundary(newmu);
		cobht:=coboundary (extendedhtpystdcocycle);
                if hcocycles=[] then
          	    cocyclefn:= function (g,h,k) return sc(g, h, k) - cobnewmu(g, h, k) - cobht(g, h, k);end;
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
	#	  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
	#	Print(cocycletest);
	#	Print("\n");
		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
                fsexp:=ExponentOfPFC(G, R, K, UCT, coho[j]);
            fsi:=FSIforAGT(G, Simples!.simples, H, adapted, expH*exponent, fsexp);
		      dimlist:= List(Simples!.simples, x-> x!.dim);
              
	        adaptedv:=CocycleValues(listG, adapted, exponent*expH);
		fring:=FusionRules(Simples, H, adaptedv, listG, exponent*expH);
                 filename:= [IdGroup(G), IdGroup(H),coho[j],[] ];
	  Print([filename, fring, dimlist, fsi], ",\n");
                    else for x in [1..Size(Hcocyclefnlist)] do                      
                extendedx:= function (g, h) if not g in H or not h in H then return 0;
                                                else return Hcocyclefnlist[x](g, h);fi;
                                                   end;
                    cobx:=coboundary(extendedx);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k)  - cobx(g, h, k) - cobnewmu(g, h, k) - cobht(g, h, k);end; 
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
	#	cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
	#	Print(cocycletest);
	#	Print("\n");
		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
                fsexp:=ExponentOfPFC(G, R, K, UCT, coho[j]);
            fsi:=FSIforAGT(G, Simples!.simples, H, adapted, expH*exponent, fsexp);
	dimlist:= List(Simples!.simples, x-> x!.dim); 
        adaptedv:=CocycleValues(listG, adapted, exponent*expH);
		fring:=FusionRules(Simples, H, adaptedv, listG, exponent*expH);
	  filename:= [IdGroup(G), IdGroup(H),coho[j], hcoho[x]];
            Print([filename, fring, dimlist, fsi], ",\n");
                od;
                 fi;
       	od;
        fi;
od;
end;







coblistprint :=function (G)
local R, K, UCT, exponent, fring, subcomp, comp, cocycletest, H, allcoho, coho, coblist, i, f, adapted, Simples, filename, cochlist, UCTH, j,mu, diff, nontrivindex, newmu, htpystdcocycle;
R:=ResolutionFiniteGroup(G, 4);
K:=TensorWithIntegers(R);
UCT:=UniversalCoefficientsTheorem(K, 3);
exponent:=UCT!.exponent;
subcomp:=SubgroupComplexes(G, R);
for comp in subcomp do
	H:=comp!.subgroup;
		Print("\n");
	Print(H);
	Print("\n");
	allcoho := List(StabHOrbitsCocycles(G, R, K, UCT, comp, 3), x-> x[1]);
	coho:= CohomologyList(G, R, K, UCT, comp, allcoho, 3);
	coblist:= CoboundaryList(UCT, comp, coho, 3);
	Print(List([1..Size(coho)], i-> [coho[i], coblist[i]]));
	od;
	end;
	
	
coboundarychk:=function(G, R, K, UCT)
local comp, subcomp,H, allcoho, coho, coblist, i;
subcomp:=SubgroupComplexes(G, R);
for comp in subcomp do
	H:=comp!.subgroup;
	allcoho := List(StabHOrbitsCocycles(G, R, K, UCT, comp, 3), x-> x[1]);
	coho:= CohomologyList(G, R, K, UCT, comp, allcoho, 3);
	coblist:= CoboundaryList(UCT, comp, coho, 3);
	for i in [1..Size(coho)] do
		if not Set(coblist[i])=[0] then Print(H, " ", coho[i], " ", coblist[i], "\n");fi;
		od;
	od;
end; 	


simpleslist :=function (G)
    local R, K, UCT, exponent, fring,g, h, k,  subcomp, comp, cocycletest, H, allcoho, coho, coblist, i, f, adapted, Simples, filename, cochlist, UCTH, j ,mu, diff, nontrivindex, newmu, htpystdcocycle, extendedhtpystdcocycle, sc, cobnewmu, cobht, cocyclefn, expH, homology, modhom, hcohomod, hcoho, hcocycles, Hcocyclefnlist, x, extendedx, cobx, dimlist, listG, adaptedv, simpleslist;
    simpleslist:=[];
    
    listG:=EnumeratorSorted(G);
R:=ResolutionFiniteGroup(G, 4);
K:=TensorWithIntegers(R);
UCT:=UniversalCoefficientsTheorem(K, 3);
exponent:=UCT!.exponent;
subcomp:=SubgroupComplexes(G, R);
#comp:=subcomp[2];
for comp in subcomp do
    H:=comp!.subgroup;
    	allcoho := List(StabHOrbitsCocycles(G, R, K, UCT, comp, 3), x-> x[1]);
	coho:= CohomologyList(G, R, K, UCT, comp, allcoho, 3);
        coblist:= CoboundaryList(UCT, comp, coho, 3);
	nontrivindex:=[];
        UCTH:=UniversalCoefficientsTheorem(comp!.complex, 2);
        expH:=UCTH!.exponent;
        if UCTH!.hombasis=[] then hcocycles:= []; 
            else
	modhom:=List(UCTH!.hombasis, x->rcv(x,expH));
	hcohomod:=NearAdditiveGroup(modhom);
	hcoho:=List(hcohomod, x -> List(x, y -> Int(y)));
	hcocycles:=List(hcoho, x-> exponent*(UCTH!.lift*x));
        Hcocyclefnlist:= List(hcocycles, x-> StandardCocycle(comp!.resolution, x, 2, exponent*expH));fi;

        
        for i in [1..Size(coho)] do if not Set(coblist[i])=[0] then Add(nontrivindex, i); else
	
		htpystdcocycle:= HomotopyStandardCocycle(R, comp!.resolution, comp!.Rchainmap, (UCT!.lift*coho[i]) mod expH*exponent, 2, expH*exponent);
		extendedhtpystdcocycle:= function (g, h) if not g in H or not h in H then return 0; else return htpystdcocycle(g, h);fi;end;
		sc:=StandardCocycle(R, UCT!.lift*coho[i] mod expH*exponent, 3, expH*exponent);
		cobht:=coboundary (extendedhtpystdcocycle);
                if hcocycles=[] then    	
                    filename:= Concatenation("G=", String(IdGroup(G)), " H=", String(IdGroup(H)), " adaptedcohoclass= ", String(coho[i]), "muclass=0" , "\n");
		Print("\n");
		Print(filename);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k) - cobht(g, h, k);end;
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
		Print(cocycletest);
		Print("\n");
		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
                Add(simpleslist, [Simples,adapted]);
                else for x in [1..Size(Hcocyclefnlist)] do
                      	filename:= Concatenation("G=", String(IdGroup(G)), " H=", String(IdGroup(H)), " adaptedcohoclass= ", String(coho[i]), "muclass=",String(hcoho[x]), "\n");
		Print("\n");
		Print(filename);
                extendedx:= function (g, h) if not g in H or not h in H then return 0;
                                                else return Hcocyclefnlist[x](g, h);fi;
                                                   end;
                    cobx:=coboundary(extendedx);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k)  - cobx(g, h, k) - cobht(g, h, k);end; 
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
		Print(cocycletest);
		Print("\n");
		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3); Add(simpleslist, [Simples, adapted]);
                         od;
                fi;fi;
                                    
                                       od;
                                        
                                       
                                        
	if not nontrivindex =[] then
	cochlist:=CochainList(comp, coblist, exponent, 3);
        for j in nontrivindex do
		filename:= Concatenation("G=", IdGroup(G), " H=", IdGroup(H), " nonadaptedcohoclass= ", String(coho[j]) , "\n"); 
		Print(filename);
		Print("\n");
        mu := StandardCocycle(comp!.resolution, cochlist[j], 2, exponent*expH);
	newmu := function (g, h) if not g in H or not h in H then return 0; else 
		return mu(g,h); fi; end;
		htpystdcocycle:= HomotopyStandardCocycle(R, comp!.resolution, comp!.Rchainmap, expH*(UCT!.lift*coho[j]) mod (expH*exponent), 2, expH*exponent);
		extendedhtpystdcocycle:= function (g, h) if not g in H or not h in H then return 0; else return htpystdcocycle(g, h);fi;end;
		sc:=StandardCocycle(R, expH*(UCT!.lift*coho[j]) mod (exponent*expH), 3, exponent*expH);
		cobnewmu:=  coboundary(newmu);
		cobht:=coboundary (extendedhtpystdcocycle);
                 if hcocycles=[] then    	
                    filename:= Concatenation("G=", String(IdGroup(G)), " H=", String(IdGroup(H)), " adaptedcohoclass= ", String(coho[i]), "muclass=0" , "\n");
		Print("\n");
		Print(filename);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k) - cobnewmu(g, h, k) - cobht(g, h, k);end;
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
		Print(cocycletest);
		Print("\n");
		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
		Add(simpleslist, [Simples, adapted]);
                 else for x in [1..Size(Hcocyclefnlist)] do
                      	filename:= Concatenation("G=", String(IdGroup(G)), " H=", String(IdGroup(H)), " adaptedcohoclass= ", String(coho[i]), "muclass=",String(hcoho[x]), "\n");
		Print("\n");
		Print(filename);
                extendedx:= function (g, h) if not g in H or not h in H then return 0;
                                                else return Hcocyclefnlist[x](g, h);fi;
                                                   end;
                    cobx:=coboundary(extendedx);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k)  - cobx(g, h, k) - cobnewmu(g, h, k) - cobht(g, h, k);end; 
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
		Print(cocycletest);
		Print("\n");
		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
                Add(simpleslist, [Simples, adapted]);
                
                od;
                 fi;
       	od;
        fi;
        
od;
return simpleslist;

end;

                                       

cocycletester :=function (G, grpno)
    local R, K, UCT, exponent, fring,g, h, k,  subcomp, comp, cocycletest, H, allcoho, coho, coblist, i, f, adapted, Simples, filename, cochlist, UCTH, j ,mu, diff, nontrivindex, newmu, htpystdcocycle, extendedhtpystdcocycle, sc, cobnewmu, cobht, cocyclefn, expH, homology, modhom, hcohomod, hcoho, hcocycles, Hcocyclefnlist, x, extendedx, cobx, dimlist, listG, adaptedv;
    listG:=EnumeratorSorted(G);
R:=ResolutionFiniteGroup(G, 4);
K:=TensorWithIntegers(R);
UCT:=UniversalCoefficientsTheorem(K, 3);
exponent:=UCT!.exponent;
subcomp:=SubgroupComplexes(G, R);
comp:=subcomp[grpno];
    H:=comp!.subgroup;
    	allcoho := List(StabHOrbitsCocycles(G, R, K, UCT, comp, 3), x-> x[1]);
	coho:= CohomologyList(G, R, K, UCT, comp, allcoho, 3);
        coblist:= CoboundaryList(UCT, comp, coho, 3);
	nontrivindex:=[];
        UCTH:=UniversalCoefficientsTheorem(comp!.complex, 2);
        expH:=UCTH!.exponent;
        if UCTH!.hombasis=[] then hcocycles:= []; 
            else
	modhom:=List(UCTH!.hombasis, x->rcv(x,expH));
	hcohomod:=NearAdditiveGroup(modhom);
	hcoho:=List(hcohomod, x -> List(x, y -> Int(y)));
	hcocycles:=List(hcoho, x-> exponent*(UCTH!.lift*x));
        Hcocyclefnlist:= List(hcocycles, x-> StandardCocycle(comp!.resolution, x, 2, exponent*expH));fi;

        
        for i in [1..Size(coho)] do if not Set(coblist[i])=[0] then Add(nontrivindex, i); else
	
		htpystdcocycle:= HomotopyStandardCocycle(R, comp!.resolution, comp!.Rchainmap, (UCT!.lift*coho[i]) mod expH*exponent, 2, expH*exponent);
		extendedhtpystdcocycle:= function (g, h) if not g in H or not h in H then return 0; else return htpystdcocycle(g, h);fi;end;
		sc:=StandardCocycle(R, UCT!.lift*coho[i] mod expH*exponent, 3, expH*exponent);
		cobht:=coboundary (extendedhtpystdcocycle);
                if hcocycles=[] then    	
                    filename:= Concatenation("G=", String(IdGroup(G)), " H=", String(IdGroup(H)), " adaptedcohoclass= ", String(coho[i]), "muclass=0" , "\n");
		Print("\n");
		Print(filename);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k) - cobht(g, h, k);end;
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
		Print(cocycletest);
		Print("\n");
                    else for x in [1..Size(Hcocyclefnlist)] do
                      	filename:= Concatenation("G=", String(IdGroup(G)), " H=", String(IdGroup(H)), " adaptedcohoclass= ", String(coho[i]), "muclass=",String(hcoho[x]), "\n");
		Print("\n");
		Print(filename);
                extendedx:= function (g, h) if not g in H or not h in H then return 0;
                                                else return Hcocyclefnlist[x](g, h);fi;
                                                   end;
                    cobx:=coboundary(extendedx);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k)  - cobx(g, h, k) - cobht(g, h, k);end; 
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
		Print(cocycletest);
		Print("\n");
                od;
                fi;fi;
                                    
                                       od;
                                        
                                       
                                        
	if not nontrivindex =[] then
	cochlist:=CochainList(comp, coblist, exponent, 3);
        for j in nontrivindex do
	
        mu := StandardCocycle(comp!.resolution, cochlist[j], 2, exponent*expH);
	newmu := function (g, h) if not g in H or not h in H then return 0; else 
		return mu(g,h); fi; end;
		htpystdcocycle:= HomotopyStandardCocycle(R, comp!.resolution, comp!.Rchainmap, expH*(UCT!.lift*coho[j]) mod (expH*exponent), 2, expH*exponent);
		extendedhtpystdcocycle:= function (g, h) if not g in H or not h in H then return 0; else return htpystdcocycle(g, h);fi;end;
		sc:=StandardCocycle(R, expH*(UCT!.lift*coho[j]) mod (exponent*expH), 3, exponent*expH);
		cobnewmu:=  coboundary(newmu);
		cobht:=coboundary (extendedhtpystdcocycle);
                 if hcocycles=[] then    	
                    filename:= Concatenation("G=", String(IdGroup(G)), " H=", String(IdGroup(H)), " adaptedcohoclass= ", String(coho[j]), "muclass=0" , "\n");
		Print("\n");
		Print(filename);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k) - cobnewmu(g, h, k) - cobht(g, h, k);end;
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
		Print(cocycletest);
		Print("\n");
	
                    else for x in [1..Size(Hcocyclefnlist)] do
                      	filename:= Concatenation("G=", String(IdGroup(G)), " H=", String(IdGroup(H)), " adaptedcohoclass= ", String(coho[j]), "muclass=",String(hcoho[x]), "\n");
		Print("\n");
		Print(filename);
                extendedx:= function (g, h) if not g in H or not h in H then return 0;
                                                else return Hcocyclefnlist[x](g, h);fi;
                                                   end;
                    cobx:=coboundary(extendedx);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k)  - cobx(g, h, k) - cobnewmu(g, h, k) - cobht(g, h, k);end; 
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
		Print(cocycletest);
		Print("\n");
	
                od;
                 fi;
       	od;
        fi;
end;


namelist:=function (arg...)
local list, G,  R, K, UCT, exponent, fring,g, h, k,  subcomp, comp, cocycletest, H, allcoho, coho, coblist, i, f, adapted, Simples, filename, cochlist, UCTH, j ,mu, diff, nontrivindex, newmu, htpystdcocycle, extendedhtpystdcocycle, sc, cobnewmu, cobht, cocyclefn, expH, homology, modhom, hcohomod, hcoho, hcocycles, Hcocyclefnlist, x, extendedx, cobx, dimlist, listG, adaptedv, fsi, fsexp;
G:=arg[1];
list:=[];
listG:=EnumeratorSorted(G);
R:=ResolutionFiniteGroup(G, 4);
K:=TensorWithIntegers(R);
UCT:=UniversalCoefficientsTheorem(K, 3);
exponent:=UCT!.exponent;
if Size(arg)>1 then subcomp:=[SubgroupComplex(G, R, arg[2])]; else subcomp:=SubgroupComplexes(G, R);fi;
for comp in subcomp do
    H:=comp!.subgroup;
    if Size(arg)>2 then coho:=[arg[3]];
        else
    	allcoho := List(StabHOrbitsCocycles(G, R, K, UCT, comp, 3), x-> x[1]);
    coho:= CohomologyList(G, R, K, UCT, comp, allcoho, 3);
    fi;
    coblist:= CoboundaryList(UCT, comp, coho, 3);
	nontrivindex:=[];
        UCTH:=UniversalCoefficientsTheorem(comp!.complex, 2);
        expH:=UCTH!.exponent;
        if UCTH!.hombasis=[] then hcocycles:= [];
            else
	modhom:=List(UCTH!.hombasis, x->rcv(x,expH));
	hcohomod:=NearAdditiveGroup(modhom);
	hcoho:=List(hcohomod, x -> List(x, y -> Int(y)));
	hcocycles:=List(hcoho, x-> exponent*(UCTH!.lift*x));
        Hcocyclefnlist:= List(hcocycles, x-> StandardCocycle(comp!.resolution, x, 2, exponent*expH));fi;
        for i in [1..Size(coho)] do if not Set(coblist[i])=[0] then Add(nontrivindex, i); else
	htpystdcocycle:= HomotopyStandardCocycle(R, comp!.resolution, comp!.Rchainmap, expH*(UCT!.lift*coho[i]) mod (expH*exponent), 2, expH*exponent);
		extendedhtpystdcocycle:= function (g, h) if not g in H or not h in H then return 0; else return htpystdcocycle(g, h);fi;end;
		sc:=StandardCocycle(R, expH*(UCT!.lift*coho[i]) mod (expH*exponent), 3, expH*exponent);
		cobht:=coboundary (extendedhtpystdcocycle);
                if hcocycles=[] then    	
     #     	    cocyclefn:= function (g,h,k) return sc(g, h, k) - cobht(g, h, k);end;
    #            adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
		#  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
	#	Print(cocycletest);
	#	Print("\n");
#		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
 #               fsexp:=ExponentOfPFC(G, R, K, UCT, coho[i]);
  #              fsi:=FSIforAGT(G, Simples!.simples, H, adapted, expH*exponent, fsexp);
#	        dimlist:= List(Simples!.simples, x-> x!.dim);
            
 #               adaptedv:=CocycleValues(listG, adapted, exponent*expH);
#		fring:=FusionRules(Simples, H, adaptedv,listG, exponent*expH);
	        filename:= [G, H,coho[i],[] ];
		    Add(list, filename);
                    
                    else for x in [1..Size(Hcocyclefnlist)] do
                extendedx:= function (g, h) if not g in H or not h in H then return 0;
                                                else return Hcocyclefnlist[x](g, h);fi;
                                                   end;
                    cobx:=coboundary(extendedx);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k)  - cobx(g, h, k) - cobht(g, h, k);end; 
        #        adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
	#	cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
	#	Print(cocycletest);
#		Print("\n");
#		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
 #               fsexp:=ExponentOfPFC(G, R, K, UCT, coho[i]);
  #              fsi:=FSIforAGT(G, Simples!.simples, H, adapted, expH*exponent, fsexp);
   #             dimlist:= List(Simples!.simples, x-> x!.dim);
#	        adaptedv:=CocycleValues(listG, adapted, exponent*expH); 
#	        fring:=FusionRules(Simples, H, adaptedv, listG, exponent*expH);
                filename:= [G, H ,coho[i], hcoho[x]];
                Add(list, filename);
	        od;
                fi;fi;
                                       od;
	if not nontrivindex =[] then
	cochlist:=CochainList(comp, coblist, exponent, 3);
        for j in nontrivindex do
        mu := StandardCocycle(comp!.resolution, cochlist[j], 2, exponent*expH);
	newmu := function (g, h) if not g in H or not h in H then return 0; else 
		return mu(g,h); fi; end;
		htpystdcocycle:= HomotopyStandardCocycle(R, comp!.resolution, comp!.Rchainmap, expH*(UCT!.lift*coho[j]) mod (expH*exponent), 2, expH*exponent);
		extendedhtpystdcocycle:= function (g, h) if not g in H or not h in H then return 0; else return htpystdcocycle(g, h);fi;end;
		sc:=StandardCocycle(R, expH*(UCT!.lift*coho[j]) mod (exponent*expH), 3, exponent*expH);
		cobnewmu:= coboundary(newmu);
		cobht:=coboundary (extendedhtpystdcocycle);
                if hcocycles=[] then
  #        	    cocyclefn:= function (g,h,k) return sc(g, h, k) - cobnewmu(g, h, k) - cobht(g, h, k);end;
 #               adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
	#	  cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
	#	Print(cocycletest);
	#	Print("\n");
#		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
 #               fsexp:=ExponentOfPFC(G, R, K, UCT, coho[j]);
#            fsi:=FSIforAGT(G, Simples!.simples, H, adapted, expH*exponent, fsexp);
		#      dimlist:= List(Simples!.simples, x-> x!.dim);
              
	       # adaptedv:=CocycleValues(listG, adapted, exponent*expH);
		#fring:=FusionRules(Simples, H, adaptedv, listG, exponent*expH);
                 filename:= [G, H,coho[j],[] ];
	            Add(list, filename);
                    
                    else for x in [1..Size(Hcocyclefnlist)] do                      
                extendedx:= function (g, h) if not g in H or not h in H then return 0;
                                                else return Hcocyclefnlist[x](g, h);fi;
                                                   end;
                    cobx:=coboundary(extendedx);
          	    cocyclefn:= function (g,h,k) return sc(g, h, k)  - cobx(g, h, k) - cobnewmu(g, h, k) - cobht(g, h, k);end; 
                adapted:= AdaptedCocycle1(G, R, H, cocyclefn);
	#	cocycletest:=IsAdaptedCocycle(G, H, adapted, expH*exponent);
	#	Print(cocycletest);
	#	Print("\n");
#		Simples:= SimplesGenerator(G, R, K, H, adapted, expH*exponent, 3);
  #              fsexp:=ExponentOfPFC(G, R, K, UCT, coho[j]);
 #           fsi:=FSIforAGT(G, Simples!.simples, H, adapted, expH*exponent, fsexp);
#	dimlist:= List(Simples!.simples, x-> x!.dim); 
 #       adaptedv:=CocycleValues(listG, adapted, exponent*expH);
#		fring:=FusionRules(Simples, H, adaptedv, listG, exponent*expH);
	  filename:= [G, H ,coho[j], hcoho[x]];
            Add(list, filename);
                od;
                 fi;
       	od;
        fi;
od;
return list;
end;

allnames:=function(n)
    local totallist, i, G;
    totallist:=[];
    for i in [2..n] do 
        Print(i);
        for G in AllSmallGroups(i) do 
            totallist:=Concatenation(totallist, namelist(G));
        od;
    od;
    return totallist;
end;
