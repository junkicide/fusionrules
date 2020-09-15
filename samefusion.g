Same_Fusion:=function(dims1, F1, dims2, F2)
    local l,P,lastbad,n,i,j,A,Q,blocks,PS1,PS2,rev, FR1, FR2, d1, d2;
    ;
    lastbad:=function(fr1, fr2, dim1, dim2, P,Q,l)
  local j,k;
   if P[l] in List([1..l-1],i->P[i]) then return true;
   fi;
   if dim2[P[l]] <>  dim1[Q[l]] then return true ;
   fi;
   for k in [1..l] do
    if fr1[Q[k]][Q[l]]<>fr2[P[k]][P[l]] then return true;
    fi;
   od;
   return false;
    end;
    
    
  mult:=function(F, i, size, y) #can be done smartly using recursion
                       local  pos, val, vect, j, k;
    if y =4 then                   
        pos1:=Filtered([1..size], x->not  IsZero(F[i][i][x]));
        pos2:=Filtered([1..size], x->not  IsZero(F[i][i][x]));fi;
    if y=3 then 
        pos1:=[i];
        pos2:=Filtered([1..size], x->not  IsZero(F[i][i][x]));
    fi;
    vect:=ListWithIdenticalEntries(size, 0);
    for j in pos1 do 
        for k in pos2 do 
                        vect:=vect + (F[i][i][j]*F[i][i][k]*F[j][k]);
                    od;
    od;
    return vect[i];
end;
presorted:= function (F, dims)
    local  n, labels, labelset, perm, finalperm, dimssorted, Fsorted,finallabels,  blocks;    
    n:=Size(dims);
      labels:=List([2..n],
                   i->[dims[i], F[i][i][i], mult(F, i, n, 3), mult(F, i, n, 4), Collected(F[i][i]) ]);
 
     
      perm:=[2..n];
      SortParallel(labels, perm);
      finalperm:=[1];
      Append(finalperm, perm);
     dimssorted:=List(finalperm, i->dims[i]);
     Fsorted:=List(finalperm, i -> List(finalperm, j->List(finalperm, k-> F[i][j][k])));
     finallabels:=[[1, 1, 1, 1,  Collected(F[1][1])]];
     Append(finallabels, labels);
      labelset:=Set(labels);
      blocks:=List(labelset,
                   l->Filtered([2..n],j->finallabels[j]=l));
      finalblocks:=[[1]];
      Append(finalblocks, blocks);
      return [dimssorted, Fsorted, finalperm, finalblocks, finallabels];
end;



PS1:=presorted(F1, dims1);
 PS2:=presorted(F2, dims2);
 if PS1[1]<>PS2[1] then
     return [false,"not the same object dimensions"];
 fi;
 if List(PS1[5], x->x[2])<>List(PS2[5]  , x-> x[2]) then 
     return  [false,"dimensions and tensor squares don't sort parallelly"];
 fi;
  if PS1[4]<>PS2[4]
  then return [false,"not the same blocks"];
 fi;
  if PS1[5]<>PS2[5]
  then return [false,"unsorted data don't match"];
 fi;
      blocks:=PS1[4];
 rev:=[];
 d1:=PS1[1];
 FR1:=PS1[2];
 d2:=PS2[1];
 FR2:=PS2[2];
 for i in [1..Size(blocks)] do
  for j in [1..Size(blocks[i])] do
      rev[blocks[i][j]]:=[i,j];
  od;
 od;

Q:=[];
for i in [1..Maximum(List(blocks,Size))] do
 A:=List(Filtered(blocks,b->Size(b)>=i),b->b[i]);
 Q:=Concatenation(Q,A);
od;
l:=1;
P:=[Q[1]];
nextinblock:=function(i)
 if rev[i][2]=Size(blocks[rev[i][1]]) then return n+1;
 fi;
 return i+1;
end;
while true do
 if P[l]>n then
  l:=l-1;
  if l=0 then return false;
  fi;
  Remove(P);
  P[l]:=nextinblock(P[l]);
  continue;
 fi;
 if lastbad(FR1, FR2,d1, d2,P,Q,l) then
  P[l]:=nextinblock(P[l]);
  continue;
 fi;
 if l=n then return true;
 fi;
 l:=l+1;
 P[l]:=blocks[rev[Q[l]][1]][1];
od;       
end;
    
