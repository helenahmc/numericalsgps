#############################################################################
##
#W  affine-def.gi           Manuel Delgado <mdelgado@fc.up.pt>
#W                          Pedro Garcia-Sanchez <pedro@ugr.es>
##
#Y  Copyright 2015-- Centro de Matemática da Universidade do Porto, Portugal and Universidad de Granada, Spain
#############################################################################
#################        Defining Affine Semigroups           ###############
###############################################################################
##
#F AffineSemigroupByGenerators(arg)
##
## Returns the affine semigroup generated by arg.
##
## The argument arg is either a list of lists of positive integers of equal length (a matrix) or consists of lists of integers with equal length
#############################################################################
InstallGlobalFunction(AffineSemigroupByGenerators, function(arg)
  local  gens, M;


  if Length(arg) = 1 then
    gens := Set(arg[1]);
  else
    gens := Set(arg);
  fi;

  if not IsRectangularTable(gens) then
    Error("The arguments must be lists of non negative integers with the same length, or a list of such lists");
  elif not ForAll(gens, l -> ForAll(l,x -> (IsPosInt(x) or x = 0))) then
    Error("The arguments must be lists of non negative integers with the same length, or a list of such lists");
  fi;
  M:= Objectify( AffineSemigroupsType, rec());

  SetGenerators(M,gens);
  SetDimension(M,Length(gens[1]));

#  Setter(IsAffineSemigroupByGenerators)(M,true);
  return M;
end);
#############################################################################
##
#O  Generators(S)
##
##  Computes a set of generators of the affine semigroup S.
##  If a set of generators has already been computed, this
##  is the set returned.
############################################################################
InstallMethod(Generators,
         "Computes a set of generators of the affine semigroup",
         [IsAffineSemigroup],1,
        function(S)
  local  basis, eq;

  if HasGenerators(S) then
      return Generators(S);
  fi;
  if HasMinimalGenerators(S) then
      return MinimalGenerators(S);
  fi;

  if HasEquations(S) then
      eq:=Equations(S);
      basis := HilbertBasisOfSystemOfHomogeneousEquations(eq[1],eq[2]);
      SetMinimalGenerators(S,basis);
      return MinimalGenerators(S);
  elif HasInequalities(S) then
      basis := HilbertBasisOfSystemOfHomogeneousInequalities(AffineSemigroupInequalities(S));
      SetMinimalGenerators(S,basis);
      return MinimalGenerators(S);
  fi;
end);

#############################################################################
##
#O  MinimalGenerators(S)
##
##  Computes the set of minimal  generators of the affine semigroup S.
##  If a set of generators has already been computed, this
##  is the set returned.
############################################################################
InstallMethod(MinimalGenerators,
         "Computes the set of minimal generators of the affine semigroup",
         [IsAffineSemigroup],1,
        function(S)
  local  basis, eq, gen;

  if HasMinimalGenerators(S) then
      return MinimalGenerators(S);
  fi;

  if HasEquations(S) then
      eq:=Equations(S);
      basis := HilbertBasisOfSystemOfHomogeneousEquations(eq[1],eq[2]);
      SetMinimalGenerators(S,basis);
      return MinimalGenerators(S);
  elif HasInequalities(S) then
      basis := HilbertBasisOfSystemOfHomogeneousInequalities(AffineSemigroupInequalities(S));
      SetMinimalGenerators(S,basis);
      return MinimalGenerators(S);
  fi;
  gen:=Generators(S);
  basis:=Filtered(gen, y->ForAll(Difference(gen,[y]),x->not((y-x) in S)));
  SetMinimalGenerators(S,basis);
  return MinimalGenerators(S);

end);

#############################################################################
##
#F  AffineSemigroupByGaps(arg)
##
##  Returns the affine semigroup determined by the gaps arg.
##  If the given set is not a set of gaps, then an error is raised.
##
#############################################################################
InstallGlobalFunction(AffineSemigroupByGaps,

function(arg)
  local  gen, M, i,j,k,c,s,t,r,mingen, Leg, H;


  if Length(arg) = 1 then
    H := Set(arg[1]);
  else
    H := Set(arg);
  fi;

  if not IsRectangularTable(H) then
    Error("The arguments must be lists of non negative integers with the same length, or a list of such lists");
  elif not ForAll(H, l -> ForAll(l,x -> (IsPosInt(x) or x = 0))) then
    Error("The arguments must be lists of non negative integers with the same length, or a list of such lists");
  fi;

#  Setter(IsAffineSemigroupByGenerators)(M,true);

  #  c:=0;                                              #Ordering the elements of H with rspect to lexicographical order
  #  for i in [1..Length(H)] do
  #      c:=c+1;
  #      for j in [c..Length(H)] do
  #          if Maximum(H[i],H[j])=H[i] then
  #          t:=H[i];
  #          H[i]:=H[j]; 
  #          H[j]:=t;
  #          fi;
  #      od;    
  #  od;   
  H:=Set(H);
 #The elements are ordered now
   gen:=IdentityMat(Length(H[1]));
   
   Leg:=Length(H[1])+1;

  #Step 1, the generators are minimal actually

  if not(H[1] in gen) then
     Error("The given set is not a set of holes of an affine semigroup");
  fi;
  
  Remove(gen,Position(gen,H[1]));
  Leg:=Length(gen);
  for k in [1..Length(gen)] do
      gen:=Concatenation(gen,[gen[k]+H[1]]);
  od;
  gen:=Concatenation(gen,[2*H[1]]);
  gen:=Concatenation(gen,[3*H[1]]);

  M:= Objectify( AffineSemigroupsType, rec());

 #Step 2, exploring a branch af the GNS tree
       
   for i in [2..Length(H)+1] do
           s:=gen;
       for j in [(Leg+1)..Length(gen)] do
           t:=[];
           for k in [1..Length(gen)] do
               if k<>Position(gen,gen[j]) then
                  t:=Concatenation(t,[gen[k]]);
               fi;
           od;
           r:=AffineSemigroup("generators",t);
           if BelongsToAffineSemigroup(gen[j],r) then
              c:=[];
           for k in [1..Length(s)] do
               if s[k]<>gen[j] then
                  c:=Concatenation(c,[s[k]]);
               fi;
           od;
           s:=c;
           fi;
       od;
       mingen:=s;
       if i=(Length(H)+1) then
            SetGaps(M,H);
            SetDimension(M,Length(H[1]));
            SetMinimalGenerators(M,mingen);
           return M;
       fi;

       if not(H[i] in mingen) then
            Error("The set is not a set of gaps of an affine semigroup");
       fi;
       
       Remove(mingen,Position(mingen,H[i]));        
       Leg:=Length(mingen);
       gen:=mingen;
       for k in [1..Length(mingen)] do
           gen:=Concatenation(gen,[mingen[k]+H[i]]);
       od;
       gen:=Concatenation(gen,[2*H[i]]);
       gen:=Concatenation(gen,[3*H[i]]);
   od;


  SetGenerators(M,gen);
  SetGaps(M,H);
  SetDimension(M,Length(H[1]));
  return M;
end);

InstallMethod(Gaps,
  "for an affine semigroups",
  [IsAffineSemigroup],
  function( M )
  local i,j,k,l,r,c,t,temp,key,sum,S,N,V,vec,P,Aff,H, A;

  if HasGaps(M) then
    return Gaps(M);
  fi;

  A:=List(Generators(M));
  c:=0;                                              #Ordering the elements of H with rspect to lexicographical order
  for i in [1..Length(A)] do
      c:=c+1;
      for j in [c..Length(A)] do
          if Maximum(A[i],A[j])=A[i] then
          t:=A[i];
          A[i]:=A[j]; 
          A[j]:=t;
          fi;
      od;    
  od;   
  S:=[];
  for j in [1..Length(A[1])] do
      S:=Concatenation(S,[[]]);
  od;
  N:=NullMat(Length(A[1]),Length(A[1]));
  V:=NullMat(Length(A[1]),Length(A[1]));                              #V is a "verification" matrix
  for r in [1..Length(A)] do
      temp:=0;                                                        #temp it is needed to not repeat the procedure if it is useless
      for j in [1..Length(A[1])] do
          if temp=0 then
            key:=0;                                                  #key it is needed to verify hat each A[r][i]=0 for all i<>j 
            for i in [1..Length(A[1])] do
                if i<>j then
                    if A[r][i]<>0 then
                      key:=1;
                    fi;
                fi;
              od;
              if key=0 then
                Append(S[j],[A[r][j]]);
                temp:=1;
              fi;     
          fi;
      od;

          for i in [1..Length(A[1])] do
              if A[r][i]=1 then
                for k in [1..Length(A[1])] do
                    if k<>i then
                        if V[i][k]=0 then
                          key:=0;
                          for l in [1..Length(A[1])] do
                              if (l<>i and l<>k) then
                                  if A[r][l]<>0 then
                                    key:=1;
                                  fi;
                              fi;
                          od;
                          if key=0 then
                          N[i][k]:=A[r][k];
                          V[i][k]:=1;
                          fi;
                        fi;
                    fi;
                od;
              fi;
          od;
      
  od;
  for i in [1..Length(A[1])] do
      for k in [1..Length(A[1])] do
          if (k<>i and V[i][k]=0) then
              Error("This afine semigroup has infinitely many gaps");
          fi;
      od;
  od;
          
  vec:=[];
  for j in [1..Length(A[1])] do
      if (Gcd(S[j])<>1) then
        Error("This affine semigroup has infinitely many gaps");
      fi;
      if FrobeniusNumber(NumericalSemigroup(S[j]))=-1 then
      sum:=0;
      else
      sum:=FrobeniusNumber(NumericalSemigroup(S[j]));                          #functions of package numericalsgps are used
      fi;
      for i in [1..Length(A[1])] do
          if i<>j then
            if FrobeniusNumber(NumericalSemigroup(S[i]))=-1 then
            temp:=0;
            else
            temp:=FrobeniusNumber(NumericalSemigroup(S[i]));
            fi;
          sum:=sum+temp*N[i][j]; 
          fi;
      od;
      vec:=Concatenation(vec,[sum]);
  od;
  P:=Cartesian(List(vec,i->[0..i]));
  H:=[];
  Aff:=AffineSemigroup("generators",A);
  for k in [1..Length(P)] do
        if (not BelongsToAffineSemigroup(P[k],Aff)) then
        H:=Concatenation(H,[P[k]]);
        fi;
  od; 
  SetGaps(M,H);
  return H;  
end);


#############################################################################
##
#O  Inequalities(S)
##
##  If S is defined by inequalities, it returns them.
############################################################################
InstallMethod(Inequalities,
         "Computes the set of equations of S, if S is a affine semigroup",
         [IsAffineSemigroup and HasInequalities],1,
        function(S)
          return AffineSemigroupInequalities(S);
end);
#############################################################################
## Full ffine semigroups
#############################################################################
##
#F  AffineSemigroupByEquations(ls,md)
##
##  Returns the (full) affine semigroup defined by the system A X=0 mod md, where the rows
## of A are the elements of ls.
##
#############################################################################
InstallGlobalFunction(AffineSemigroupByEquations, function(arg)
  local  ls, md, M;

  if Length(arg) = 1 then
    ls := arg[1][1];
    md := arg[1][2];
  else
    ls := arg[1];
    md := arg[2];
  fi;

  if not(IsHomogeneousList(ls)) or not(IsHomogeneousList(md)) then
    Error("The arguments must be homogeneous lists.");
  fi;

  if not(ForAll(ls,IsListOfIntegersNS)) then
    Error("The first argument must be a list of lists of integers.");
  fi;

  if not(md = [] or IsListOfIntegersNS(md)) then
    Error("The second argument must be a lists of integers.");
  fi;

  if not(ForAll(md,x->x>0)) then
    Error("The second argument must be a list of positive integers");
  fi;

  if not(Length(Set(ls, Length))=1) then
    Error("The first argument must be a list of lists all with the same length.");
  fi;

  M:= Objectify( AffineSemigroupsType, rec());
  SetEquations(M,[ls,md]);
  SetDimension(M,Length(ls[1]));

#  Setter(IsAffineSemigroupByEquations)(M,true);
#  Setter(IsFullAffineSemigroup)(M,true);
  return M;
end);

#############################################################################
##
#F  AffineSemigroupByInequalities(ls)
##
##  Returns the (full) affine semigroup defined by the system  ls*X>=0 over
##  the nonnegative integers
##
#############################################################################
InstallGlobalFunction(AffineSemigroupByInequalities, function(arg)
  local  ls, M;

  if Length(arg) = 1 then
    ls := Set(arg[1]);
  else
    ls := Set(arg);
  fi;

  if not IsRectangularTable(ls) then
    Error("The arguments must be lists of integers with the same length, or a list of such lists");
  fi;

  M:= Objectify( AffineSemigroupsType, rec());

  SetAffineSemigroupInequalities(M,ls);
  SetDimension(M,Length(ls[1]));
 # Setter(IsAffineSemigroupByEquations)(M,true);
 # Setter(IsFullAffineSemigroup)(M,true);
  return M;
end);


#############################################################################

#############################################################################
##
#F  AffineSemigroup(arg)
##
##  This function's first argument may be one of:
##  "generators", "equations", "inequalities"...
##
##  The following arguments must conform to the arguments of
##  the corresponding function defined above.
##  By default, the option "generators" is used, so,
##  gap> AffineSemigroup([1,3],[7,2],[1,5]);
##  <Affine semigroup in 3-dimensional space, with 3 generators>
##
##
#############################################################################
InstallGlobalFunction(AffineSemigroup, function(arg)

  if IsString(arg[1]) then
    if arg[1] = "generators" then
      return AffineSemigroupByGenerators(Filtered(arg, x -> not IsString(x))[1]);
    elif arg[1] = "equations" then
      return AffineSemigroupByEquations(Filtered(arg, x -> not IsString(x))[1]);
    elif arg[1] = "inequalities" then
      return AffineSemigroupByInequalities(Filtered(arg, x -> not IsString(x))[1]);
    elif arg[1] = "gaps" then
      return AffineSemigroupByGaps(Filtered(arg, x -> not IsString(x))[1]);
    else
      Error("Invalid first argument, it should be one of: \"generators\", \"minimalgenerators\", \"gaps\" ");
    fi;
  elif Length(arg) = 1 and IsList(arg[1]) then
    return AffineSemigroupByGenerators(arg[1]);
  else
    return AffineSemigroupByGenerators(arg);
  fi;
  Error("Invalid argumets");
end);

#############################################################################
##
#P  IsAffineSemigroupByGenerators(S)
##
##  Tests if the affine semigroup S was given by generators.
##
#############################################################################
 # InstallMethod(IsAffineSemigroupByGenerators,
 #         "Tests if the affine semigroup S was given by generators",
 #         [IsAffineSemigroup],
 #         function( S )
 #   return(HasGeneratorsAS( S ));
 # end);
#############################################################################
##
#P  IsAffineSemigroupByMinimalGenerators(S)
##
##  Tests if the affine semigroup S was given by its minimal generators.
##
#############################################################################
 # InstallMethod(IsAffineSemigroupByMinimalGenerators,
 #         "Tests if the affine semigroup S was given by its minimal generators",
 #         [IsAffineSemigroup],
 #         function( S )
 #   return(HasIsAffineSemigroupByMinimalGenerators( S ));
 # end);
#############################################################################
##
#P  IsAffineSemigroupByEquations(S)
##
##  Tests if the affine semigroup S was given by equations or equations have already been computed.
##
 #############################################################################
 # InstallMethod(IsAffineSemigroupByEquations,
 #         "Tests if the affine semigroup S was given by equations",
 #         [IsAffineSemigroup],
 #         function( S )
 #   return(HasEquationsAS( S ));
 # end);

#############################################################################
##
#P  IsAffineSemigroupByInequalities(S)
##
##  Tests if the affine semigroup S was given by inequalities or inequalities have already been computed.
##
# #############################################################################
 # InstallMethod(IsAffineSemigroupByInequalities,
 #         "Tests if the affine semigroup S was given by inequalities",
 #         [IsAffineSemigroup],
 #         function( S )
 #   return(HasInequalitiesAS( S ));
 # end);

#############################################################################
##
#P  IsFullAffineSemigroup(S)
##
##  Tests if the affine semigroup S has the property of being full.
##
# Detects if the affine semigroup is full: the nonnegative
# of the the group spanned by it coincides with the semigroup
# itself; or in other words, if a,b\in S and a-b\in \mathbb N^n,
# then a-b\in S
#############################################################################
 InstallMethod(IsFullAffineSemigroup,
         "Tests if the affine semigroup S has the property of being full",
         [IsAffineSemigroup],1,
         function( S )
   local  gens, eq, h, dim;

   if HasEquations(S) then
     return true;
   fi;


   gens := GeneratorsOfAffineSemigroup(S);
   if gens=[] then
       return true;
   fi;
   dim:=Length(gens[1]);
   eq:=EquationsOfGroupGeneratedBy(gens);
   if eq[1]=[] then
       h:=IdentityMat(dim);
   else
       h:=HilbertBasisOfSystemOfHomogeneousEquations(eq[1],eq[2]);
   fi;
  if ForAll(h, x->BelongsToAffineSemigroup(x,S)) then
    SetEquations(S,eq);
    #Setter(IsAffineSemigroupByEquations)(S,true);
    #Setter(IsFullAffineSemigroup)(S,true);
    return true;
  fi;
  return false;

end);


#############################################################################
 ##
 #M  PrintObj(S)
 ##
 ##  This method for affine semigroups.
 ##
 #############################################################################
InstallMethod( PrintObj,
        "Prints an Affine Semigroup",
        [ IsAffineSemigroup],
        function( S )
  if HasGenerators(S) then
    Print("AffineSemigroup( ", Generators(S), " )\n");
  elif HasEquations(S) then
    Print("AffineSemigroupByEquations( ", Equations(S), " )\n");
  elif HasInequalities(S) then
    Print("AffineSemigroupByInequalities( ", Inequalities(S), " )\n");
  else
    Print("AffineSemigroup( ", GeneratorsOfAffineSemigroup(S), " )\n");
  fi;
end);



#############################################################################
##
#M  ViewString(S)
##
##  This method for affine semigroups.
##
#############################################################################
InstallMethod( ViewString,
        "Displays an Affine Semigroup",
        [IsAffineSemigroup],
        function( S )
  if HasMinimalGenerators(S) then
        return Concatenation("Affine semigroup in ", String(Length(MinimalGenerators(S)[1]))," dimensional space, with ", String(Length(MinimalGenerators(S))), " generators");
    elif HasGenerators(S) then
        return Concatenation("Affine semigroup in ", String(Length(Generators(S)[1]))," dimensional space, with ", String(Length(Generators(S))), " generators");
    else
        return ("<Affine semigroup>");
    fi;
end);

#############################################################################
##
#M  String(S)
##
##  This method for affine semigroups.
##
#############################################################################
InstallMethod(String,[IsAffineSemigroup],ViewString);

#############################################################################
##
#M  ViewObj(S)
##
##  This method for affine semigroups.
##
#############################################################################
InstallMethod( ViewObj,
        "Displays an Affine Semigroup",
        [IsAffineSemigroup],
        function( S )
  if HasMinimalGenerators(S) then
        Print("<Affine semigroup in ", Length(MinimalGenerators(S)[1])," dimensional space, with ", Length(MinimalGenerators(S)), " generators>");
    elif HasGenerators(S) then
        Print("<Affine semigroup in ", Length(Generators(S)[1])," dimensional space, with ", Length(Generators(S)), " generators>");
    else
        Print("<Affine semigroup>");
    fi;
end);



#############################################################################
##
#M  Display(S)
##
##  This method for affine semigroups. ## under construction... (= View)
##
#############################################################################
InstallMethod( Display,
        "Displays an Affine Semigroup",
        [IsAffineSemigroup],
        function( S )
    if HasMinimalGenerators(S) then
        Print("<Affine semigroup in ", Length(MinimalGenerators(S)[1]),"-dimensional space, with ", Length(MinimalGenerators(S)), " generators>");
    elif HasGenerators(S) then
        Print("<Affine semigroup in ", Length(Generators(S)[1]),"-dimensional space, with ", Length(Generators(S)), " generators>");
    else
        Print("<Affine semigroup>");
    fi;
end);



 ####################################################
 ####################################################


 ############################################################################
 ##
 #M Methods for the comparison of affine semigroups.
 ##
 InstallMethod( \=,
         "for two numerical semigroups",
         [IsAffineSemigroup and IsAffineSemigroupRep,
          IsAffineSemigroup and IsAffineSemigroupRep],
         function(x, y )
   local  genx, geny;

   if Dimension(x) <> Dimension(y) then
     return false;
   fi;

   if  HasEquations(x) and HasEquations(y) and
       Equations(x) = Equations(y) then
     return true;

   elif HasInequalities(x) and HasInequalities(y) and
     AffineSemigroupInequalities(x) = AffineSemigroupInequalities(y) then
     return true;

   elif HasGenerators(x) and HasGenerators(y) and
     Generators(x) = Generators(y) then
     return  true;

   elif HasGaps(x) and HasGaps(y) and
     Gaps(x) = Gaps(y) then
     return  true;

   elif HasGenerators(x) and HasGenerators(y) and not(EquationsOfGroupGeneratedBy(Generators(x))=EquationsOfGroupGeneratedBy(Generators(y))) then
     return false;
   fi;
   genx:=GeneratorsOfAffineSemigroup(x);
   geny:=GeneratorsOfAffineSemigroup(y);
   return ForAll(genx, g-> g in y) and
          ForAll(geny, g-> g in x);
 end);

 ## x < y returns true if:  (dimension(x)<dimension(y)) or (x is (strictly) contained in y) or (genx < geny), where genS is the *current* set of generators of S...
 InstallMethod( \<,
         "for two affine semigroups",
         [IsAffineSemigroup,IsAffineSemigroup],
         function(x, y )
   local  genx, geny;

   if Dimension(x) < Dimension(y) then
     return true;
   fi;

   genx:=GeneratorsOfAffineSemigroup(x);
   geny:=GeneratorsOfAffineSemigroup(y);
   if ForAll(genx, g-> g in y) and not ForAll(geny, g-> g in x) then
     return true;
   fi;

   return genx < geny;
end );


#############################################################################
##
#F AsAffineSemigroup(S)
##
## Takes a numerical semigroup as argument and returns it as affine semigroup
##
#############################################################################
InstallGlobalFunction(AsAffineSemigroup, function(s)
    local msg;

    if not(IsNumericalSemigroup(s)) then
        Error("The argument must be a numerical semigroup");
    fi;

    msg:=MinimalGeneratingSystem(s);
    return AffineSemigroup(List(msg, x->[x]));

end);
