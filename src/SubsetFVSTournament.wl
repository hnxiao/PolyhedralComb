(* ::Package:: *)

BeginPackage["SubsetFVSTournament`",{"Graphs`"}]


gentourngAdjacencyMatrix::usage="BlossomSystem[g] returns the linear system Ax<=b of odd set constraints in list {A,b}.";
TriangleVertexList::usage="BlossomMatrix[g] returns the LHS matrix of odd set constraints Ax<=b.";
SpecialVertexSets::usage="BlossomVector[g] returns the RHS vector of odd set constraints Ax<=b.";
IdealPairQ::usage="BlossomVector[g] returns the RHS vector of odd set constraints Ax<=b.";
NIVertexSetQ::usage="BlossomVector[g] returns the RHS vector of odd set constraints Ax<=b.";
NIVertexSets::usage="BlossomVector[g] returns the RHS vector of odd set constraints Ax<=b.";
MNIVertexSetQ::usage="BlossomVector[g] returns the RHS vector of odd set constraints Ax<=b.";
MNIVertexSets::usage="BlossomVector[g] returns the RHS vector of odd set constraints Ax<=b.";


Begin["`Private`"]


gentourngAdjacencyMatrix[l_List]:=Module[{n,mat,auxmat},
	n=Abs[1/2 (1-Sqrt[1+8*Length@l])];
	mat=SparseArray[Rule[#1,#2]&@@@Thread@{Flatten[Table[{i,j+1},{i,n},{j,i,n}],1],l}];
	mat=Append[mat,ConstantArray[0,n+1]];
	auxmat=SparseArray[{i_,j_}/;i<j->1,{n+1,n+1}];mat+Transpose[auxmat-mat]];

TriangleVertexList[g_Graph,v_]:=Union@@@Apply[List,FindCycle[{g,v},{3},All],2];

SpecialVertexSets[g_Graph,n_Integer]:=Module[{vl},
	vl=Select[VertexList@g,UnsameQ[TriangleVertexList[g,#],{}]&];
	(*Make sure every vertex is in a triangle.*)
	Subsets[vl,{n}]];

IdealPairQ[g_Graph,s_List]:=Module[{vl,el},
	vl=VertexList@g;
	el=Apply[Union,TriangleVertexList[g,#]&/@s];
	IdealQ@@HypergraphCoveringSystem[vl,el]];

NIVertexSetQ[g_Graph,vs_List]:=Module[{},
	Not@IdealPairQ[g,vs]];

NIVertexSets[g_Graph,n_Integer]:=Module[{vs},
	vs=SpecialVertexSets[g,n];
	Select[vs,NIVertexSetQ[g,#]&]];

MNIVertexSetQ[g_Graph,nivs_List]:=Module[{subg,subnivs,size,test},
	size=Length@nivs;
	If[size>2,subnivs=Union@@Table[NIVertexSets[g,i],{i,2,size-1}],subnivs={}];
	subg=Subgraph[g,#]&/@Subsets[VertexList@g,{VertexCount@g-1}];
	subnivs=Union[subnivs,Apply[Union,NIVertexSets[#,size]&/@subg]];
	NoneTrue[TrueQ][SubsetQ[nivs,#]&/@subnivs]];

MNIVertexSets[g_Graph,n_Integer]:=Module[{nivs},
	nivs=NIVertexSets[g,n];
	Select[nivs,MNIVertexSetQ[g,#]&]];


End[]


EndPackage[]
