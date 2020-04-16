#
# CatReps: Representations and cohomology of finite categories
#
# Implementations
#

##
InstallGlobalFunction( ConvertToMapOfFinSets,
   function( objects, gen )
        local O, T, S, G, j, i;
	
	for O in objects do
		if Length(Intersection(gen,O)) > 0 then
			T := FinSet(O);
			break;
		fi;
	od;
	
	if not IsBound( T ) then
		Error( "unable to find target set\n" );
	fi;
	
	S := FinSet(PositionsProperty(Flat(objects),i->IsBound(gen[i])));
	
	G := [];
	j := 1;
	for i in S do
		G[j] := [ i, gen[i] ];  # gen[i] is sure to be bound
                j := j + 1;
	od;
	
	return MapOfFinSets( S, G, T );
	
end );

##
InstallMethod( ConcreteCategoryForCAP,
        "for a list",
        [ IsList ],
        
  function( L )
    local C, c;
    
    C := Subcategory( FinSets, "A finite concrete category" : FinalizeCategory := false );
    
    SetFilterObj( C, IsFiniteConcreteCategory );
    
    AddIsAutomorphism( C,
      function( alpha )
        return IsAutomorphism( UnderlyingCell( alpha ) );
    end );
    
    AddInverse( C,
      function( alpha )
        return Inverse( UnderlyingCell( alpha ) ) / CapCategory( alpha );
    end );
    
    c := ConcreteCategory( L );
    
    C!.ConcreteCategoryRecord := c;
    
    SetSetOfObjects( C, List( c.objects, o -> FinSet( o ) / C ) );
    SetSetOfGeneratingMorphisms( C, List( c.generators, g -> ConvertToMapOfFinSets( c.objects, g ) / C ) );
    
    Finalize( C );
    
    return C;
    
end );

##
InstallMethod( Algebroid,
        "for a homalg ring and a finite category",
        [ IsHomalgRing and IsCommutative, IsFiniteConcreteCategory ],
        
  function( k, C )
    local q, kq, rel;
    
    TryNextMethod( );
    
    #q := ...
    
    #kq := PathAlgebra( k, q )
    
    #rel := ...
    
    kq := Algebroid( kq, rel );
    
    SetUnderlyingCategory( kq, C );
    
    SetIsLinearClosureOfACategory( kq, true );
    
    return kq;
    
end );

##
InstallMethod( DecomposeOnceByRandomEndomorphism,
        "for an object in a Hom-category",
        [ IsCapCategoryObjectInHomCategory ],
        
  function( F )
    local d, n, endbas, k, b, alpha, i, alpha2, keremb;
    
    d := Maximum( List( ValuesOnAllObjects( F ), Dimension ) );
    
    endbas := ShallowCopy( BasisOfExternalHom( F, F ) );
    
    Add( endbas, ZeroMorphism( F, F ) );
    
    k := CommutativeRingOfLinearCategory( CapCategory( F ) );
    
    n := Int( Log2( Float( d ) ) ) + 1;
    
    for b in Reversed( [ 2 .. Length( endbas ) ] ) do
        
        alpha := endbas[b] + Random( k ) * endbas[b-1];
        
        SetFilterObj( alpha, IsMultiplicativeElementWithInverse );
        
        for i in [ 1 .. n ] do
            alpha2 := PreCompose( alpha, alpha );
            if IsCongruentForMorphisms( alpha, alpha2 ) then
                break;
            fi;
            alpha := alpha2;
        od;
        
        if IsZero( alpha ) then
            continue;
        fi;
        
        keremb := KernelEmbedding( alpha );
        
        if IsZero( keremb ) then
            continue;
        fi;
        
        return [ ImageEmbedding( alpha ), keremb ];
        
    od;
    
    return fail;
    
end );

##
InstallMethod( WeakDirectSumDecomposition,
        "for an object in a Hom-category",
        [ IsCapCategoryObjectInHomCategory ],
        
  function( F )
    local queue, summands, eta, result;
    
    queue := [ IdentityMorphism( F ) ];
    
    summands := [ ];
    
    while not IsEmpty( queue ) do
        
        eta := Remove( queue );
        
        result := DecomposeOnceByRandomEndomorphism( Source( eta ) );
        
        if result = fail then
            Add( summands, eta );
        else
            Append( queue, List( result, emb -> PreCompose( emb, eta ) ) );
        fi;
        
    od;
    
    return summands;
    
end );

##
InstallMethod( RecordOfCategory,
        "for an algebroid",
        [ IsAlgebroid ],
        
  function( kq )

    return rec( domain := List( SetOfGeneratingMorphisms( kq ), a -> VertexIndex( UnderlyingVertex( Source( a ) ) ) ),
                codomain := List( SetOfGeneratingMorphisms( kq ), a -> VertexIndex( UnderlyingVertex( Range( a ) ) ) ),
                );
    
end );

##
InstallMethod( RecordOfCatRep,
        "for an object in a Hom-category",
        [ IsCapCategoryObjectInHomCategory ],
        
  function( F )

    return rec( category := RecordOfCategory( Source( CapCategory( F ) ) ),               
                genimages := List( ValuesOnAllGeneratingMorphisms( F ), a -> Eval( UnderlyingMatrix( a ) )!.matrix ),
                dimension := List( ValuesOnAllObjects( F ), Dimension ),
                field := CommutativeRingOfLinearCategory( Source( CapCategory( F ) ) )!.ring
                );
    
end );

## EmbeddingOfSubRepresentation = Spin in catreps
## Source( EmbeddingOfSubRepresentation ) = SubmoduleRep in catreps
InstallMethod( EmbeddingOfSubRepresentation,
        "for a list and an object in a Hom-category",
        [ IsList, IsCapCategoryObjectInHomCategory ],
        
  function( eta, F )
    local kq, objects, morphisms, subrep, embedding;
    
    kq := Source( CapCategory( F ) );
    
    eta := List( eta, function( eta_o ) if IsMonomorphism( eta_o ) then return eta_o; fi; return ImageEmbedding( eta_o ); end );
    
    objects := List( eta, Source );
    morphisms := List(
                      SetOfGeneratingMorphisms( kq ),
                      m ->
                      LiftAlongMonomorphism( eta[VertexIndex( UnderlyingVertex( Range( m ) ) )],
                              PreCompose( eta[VertexIndex( UnderlyingVertex( Source( m ) ) )], F( m ) ) ) );
    
    subrep := AsObjectInHomCategory( kq, objects, morphisms );
    
    embedding := AsMorphismInHomCategory( subrep, eta, F );
    
    SetIsMonomorphism( embedding, true );
    
    return embedding;
    
end );

##
InstallMethod( WeakDirectSumDecompositionOld,
        "for an object in a Hom-category",
        [ IsCapCategoryObjectInHomCategory ],
        
  function( F )
    local f, d, kq, k, objects, morphisms, summands, embeddings;
    
    f := RecordOfCatRep( F );
    
    d := Decompose( f );
    
    kq := Source( CapCategory( F ) );
    
    k := CommutativeRingOfLinearCategory( kq );
    
    d := List( d, eta -> List( [ 1 .. Length( eta ) ], i -> VectorSpaceMorphism( VectorSpaceObject( Length( eta[i] ), k ), eta[i], F( kq.(i) ) ) ) );
    
    return List( d, eta -> EmbeddingOfSubRepresentation( eta, F ) );
    
end );
