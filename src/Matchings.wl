(* ::Package:: *)

BeginPackage["Matchings`",{"Graphs`"}]

BlossomSystem::usage="BlossomSystem[g] returns the linear system Ax<=b of odd set constraints in list {A,b}.";
BlossomMatrix::usage="BlossomMatrix[g] returns the LHS matrix of odd set constraints Ax<=b.";
BlossomVector::usage="BlossomVector[g] returns the RHS vector of odd set constraints Ax<=b.";

EdgeDominatingMatrix::usage="EdgeDominatingMatrix[g,pl] returns the Rothblum stability matrix.";
PreferenceList::usage="PreferenceList[g] returns a random prefrence list in edges.";
SubPreferenceList::usage="SubPreferenceList[subg,pl] returns the preference list restricted to subgraph subg.";

BirkhoffSystem::usage="BirkhoffSystem[g] returns the Birkhoff system for bipartite graph g"
EdmondsSystem::usage="EdmondsSystem[g] returns the fractional matching system.";
RothblumSystem::usage="RothblumSystem[g,p] returns the linear systme Ax<=b defining fractional stable matching polytope";
EdmondsRothblumSystem::usage="EdmondsRothblumSystem[g,p] returns the linear systme Ax<=b defining fractional stable matching polytope";


Begin["`Private`"]


(*** GRAPH MATRICES ***)


(* Edmonds odd set system or blossom system *)
BlossomSystem[g_Graph]:=Module[{el,vl,subl,mat,vec},
	el=EdgeList[g];
	vl=VertexList[g];
	subl=Select[Subsets[vl,{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	mat=SparseArray[{i_,j_}/;(Length@Intersection[subl[[i]],List@@el[[j]]]==2):>1,{Length@subl,Length@el}];
	vec=(Length/@subl-1)/2;
	{mat,vec}];

BlossomMatrix[g_Graph]:=BlossomSystem[g][[1]];

BlossomVector[g_Graph]:=BlossomSystem[g][[2]];


EdgeDominatingMatrix[g_Graph,pl_List]:=Module[{cel,cpl,del},
(*EdgeDominatingMatrix is NOT sensitive to the order of PreferenceList*)
	cel=Sort/@EdgeList@g;(*Put edges in canonical form*)
	cpl=Map[Sort,pl,{2}];(*Put edges in canonical form*)
	del=dominatingEdges[cpl,#]&/@cel;
	Outer[Boole[MemberQ[#1,#2]]&,del,cel,1]];
(*Private function: Dominating edges*)
dominatingEdges[cpl_List,ce_UndirectedEdge]:=Module[{epl},
(*Edges are assumed to be in canonial form*)
	epl=Select[cpl,MemberQ[#,ce]&];
	Apply[Union,Take[#,Position[#,ce][[1]][[1]]]&/@epl]];

PreferenceList[g_Graph]:=Module[{},
	Map[RandomSample[IncidenceList[g,#]]&,Sort@VertexList@g]];

SubPreferenceList[subg_Graph,pl_List]:=Module[{cel,cpl,subpl},
	cel=Sort/@EdgeList@subg;
	cpl=Map[Sort,pl,{2}];
	subpl=Intersection[#,cel]&/@cpl;
	Select[subpl,UnsameQ[#,{}]&]];
(*
EdgeDominatingMatrix[g_Graph,pl_List]:=Module[{el},
	el=List@@@EdgeList@g;
	Outer[Boole[#1==#2\[Or]IntersectingQ[#1,#2]&&
		OrderedQ@{Position[pl[[Intersection[#1,#2][[1]]]],Complement[#2,Intersection[#1,#2]][[1]]],
				Position[pl[[Intersection[#1,#2][[1]]]],Complement[#1,Intersection[#1,#2]][[1]]]}]&,el,el,1]];
PreferenceVertexList[g_Graph]:=Module[{},
	Map[RandomSample[AdjacencyList[g,#]]&,Sort@VertexList[g]]];
*)


BirkhoffSystem[g_Graph]:=Module[{A,b},
	A=Join[IncidenceMatrix@g,-IdentityMatrix[EdgeCount@g]];
	b=Join[ConstantArray[1,VertexCount@g],ConstantArray[0,EdgeCount@g]];
	{A,b}];

EdmondsSystem[g_Graph]:=Module[{A,b},
	{A,b}=BirkhoffSystem@g;
	A=Join[A,BlossomMatrix@g];
	b=Join[b,BlossomVector@g];
	{A,b}];

RothblumSystem[g_Graph,p_List]:=Module[{A,b},
	{A,b}=BirkhoffSystem[g];
	A=Join[A,-EdgeDominatingMatrix[g,p]];
	b=Join[b,-ConstantArray[1,EdgeCount@g]];
	{A,b}];

EdmondsRothblumSystem[g_Graph,p_List]:=Module[{A,b},
	{A,b}=RothblumSystem[g,p];
	A=Join[A,BlossomMatrix[g]];
	b=Join[b,BlossomVector[g]];
	{A,b}];


End[]


EndPackage[]
