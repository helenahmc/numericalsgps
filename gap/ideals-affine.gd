#############################################################################
##
#W  ideals-affine.gd           Manuel Delgado <mdelgado@fc.up.pt>
#W                          Pedro A. Garcia-Sanchez <pedro@ugr.es>
#W                          Helena Martin Cruz <Helena.mc18@gmail.com>
##
##
#Y  Copyright 2019 by Manuel Delgado,
#Y  Pedro Garcia-Sanchez and Helena Martin Cruz
#Y  We adopt the copyright regulations of GAP as detailed in the
#Y  copyright notice in the GAP manual.
##
#############################################################################

#############################################################################
##
#R  IsIdealOfAffineSemigroupRep
##
##  The representation of an ideal of an affine semigroup.
##
#############################################################################
DeclareRepresentation( "IsIdealOfAffineSemigroupRep", IsAttributeStoringRep,
        [] );

#############################################################################
##
#C  IsIdealOfAffineSemigroup
##
##  The category of ideals of affine semigroups.
##
#############################################################################
DeclareCategory( "IsIdealOfAffineSemigroup", IsAdditiveMagma and IsIdealOfAffineSemigroupRep);



# Elements of ideals of affine semigroups are integers tuples, so ideals of
# affine semigroups are collections of integers tuples.
BindGlobal( "IdealsOfAffineSemigroupsType",
        NewType( CollectionsFamily( CollectionsFamily(CyclotomicsFamily)),
                 IsIdealOfAffineSemigroup));


#############################################################################
##
#F IdealOfAffineSemigroup(l,S)
##
## l is a list of integers tuples and S an affine semigroup
##
## returns the ideal of S generated by l.
##
#############################################################################
DeclareGlobalFunction("IdealOfAffineSemigroup");
DeclareAttribute( "UnderlyingASIdeal", IsIdealOfAffineSemigroup);


#############################################################################
##
#A  Generators(I)
#A  GeneratorsOfIdealOfAffineSemigroup(I)
##
##  Returns a set of generators of the ideal I.
############################################################################
DeclareAttribute( "Generators", IsIdealOfAffineSemigroup);
DeclareSynonymAttr( "GeneratorsOfIdealOfAffineSemigroup", Generators);


#############################################################################
##
#F AmbientAffineSemigroupOfIdeal(I)
##
##  Returns the ambient semigroup of the ideal I.
############################################################################
DeclareGlobalFunction("AmbientAffineSemigroupOfIdeal");


#############################################################################
##
#P  IsIntegralIdealOfAffineSemigroup(I)
##
##  Detects if the ideal I is contained in its ambient affine semigroup
##
#############################################################################
DeclareProperty("IsIntegral", IsIdealOfAffineSemigroup);
DeclareSynonym("IsIntegralIdealOfAffineSemigroup", IsIntegral);



#############################################################################
##
#F SumIdealsOfAffineSemigroup(I,J)
##
## returns the sum of the ideals I and J (in the same ambient affine semigroup)
#############################################################################
DeclareGlobalFunction("SumIdealsOfAffineSemigroup");


#############################################################################
##
#F UnionIdealsOfAffineSemigroup(I,J)
##
## returns the union of the ideals I and J (in the same ambient affine semigroup)
#############################################################################
DeclareGlobalFunction("UnionIdealsOfAffineSemigroup");



#############################################################################
##
#F IntersectionPrincipalIdealsOfAffineSemigroup(I,J)
##
## returns the intersection of the principal ideals I and J (in the same ambient affine semigroup)
#############################################################################
DeclareOperation("IntersectionPrincipalIdealsOfAffineSemigroup",[IsIdealOfAffineSemigroup,IsIdealOfAffineSemigroup]);


#############################################################################
##
#F IntersectionIdealsOfAffineSemigroup(I,J)
##
## returns the intersection of the ideals I and J (in the same ambient affine semigroup)
#############################################################################
DeclareGlobalFunction("IntersectionIdealsOfAffineSemigroup");


#############################################################################
##
#F SubtractPrincipalIdealsOfAffineSemigroup(I,J)
##
## returns the ideal I-J of the principal ideals I and J (in the same ambient affine semigroup)
#############################################################################
DeclareOperation("SubtractPrincipalIdealsOfAffineSemigroup",[IsIdealOfAffineSemigroup,IsIdealOfAffineSemigroup]);

#############################################################################
##
#F SubtractIdealsOfAffineSemigroup(I,J)
##
## returns the ideal I-J of the ideals I and J (in the same ambient affine semigroup)
#############################################################################
DeclareGlobalFunction("SubtractIdealsOfAffineSemigroup");

#############################################################################
##
#O  BelongsToIdealOfAffineSemigroup(n,I)
##
##  Tests if the integer tuple n belongs to the ideal I.
##
#############################################################################
DeclareOperation("BelongsToIdealOfAffineSemigroup",[IsHomogeneousList,IsIdealOfAffineSemigroup]);


#############################################################################
##
#F MultipleOfIdealOfAffineSemigroup(n,I)
##
## n is a non negative integer tuple and I is an ideal
## returns the multiple nI (I+...+I n times) of I
#############################################################################
DeclareGlobalFunction("MultipleOfIdealOfAffineSemigroup");


#############################################################################
##
#A MinimalGenerators(I)
#A MinimalGeneratingSystemOfIdealOfAffineSemigroup(I)
##
## The argument I is an ideal of an affine semigroup
## returns the minimal generating system of I.
##
#############################################################################
DeclareAttribute( "MinimalGenerators", IsIdealOfAffineSemigroup);
DeclareSynonymAttr("MinimalGeneratingSystemOfIdealOfAffineSemigroup", MinimalGenerators);


#############################################################################
##
#F  TranslationOfIdealOfAffineSemigroup(k,I)
##
##  Given an ideal I of an affine semigroup S and an integer k
##  returns an ideal of the affine semigroup S generated by
##  {i1+k,...,in+k} where {i1,...,in} is the system of generators of I.
##
#############################################################################
DeclareGlobalFunction("TranslationOfIdealOfAffineSemigroup");

#############################################################################
##
#O  MaximalIdealOfAffineSemigroup(S)
##
##  Returns the maximal ideal of the affine semigroup S.
##
#############################################################################
DeclareOperation("MaximalIdeal",[IsAffineSemigroup]);