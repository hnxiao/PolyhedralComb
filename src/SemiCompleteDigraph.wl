(* ::Package:: *)

Tournament::usage="Tournament[n] returns a random tournament.";
SemiCompleteDigraph::usage="SemiCompleteDigraph[n,m] returns a random semicomplete digraph with m opposite oriented arcs.";

GoodTournament::usage="GoodTournament[n] TRIES to return a strongly connected random tournament without obstructions within 1000 attempts.";
GoodSemiCompleteDigraph::usage="GoodSemiCompleteDigraph[n,m] TRIES to return a strongly connected random semicomplete digraph without obstructions within 1000 attempts.";
BFSVertexPartition::usage="BFSVertexPartition[d,r] returns a bfs vertex partition with root r. Moreover, each parition is returned in topological order if it is acyclic, otherwise a cycle list in this partition is accompanied.";
MaxOutDegreeVertexList::usage="MaxOutDegreeVertexList[d] returns all vertices with maximum out degree.";
MinInDegreeVertexList::usage="MinInDegreeVertexList[d] returns all vertices with minimum in degree.";
BFSVertexPartitionList::usage="BFSVertexPartitionList[d] returns all bfs vertex partitions rooted at vertices with maximum outdegree by using BFSVertexPartition[d,r].";
HangingCycleList::usage="HangingCycleList[d,v] returns all good distinct cycles incident to vertex v in digrah v.";

PossibleDigraphList::usage="PossibleDigraphList[d] returns all possible orientions in a semicomplete digraph with a given supporting structure.";


(*FVS in semicomplete digraphs*)
Tournament[n_Integer]:=Module[{g,t},
	g=CompleteGraph[n];
	t=DirectedGraph[g,"Random",VertexLabels->"Name"]];

SemiCompleteDigraph[n_Integer,m_Integer:1]/;1<=m<=n (n-1)/2:=Module[{t,d,arl},
	t=Tournament[n];
	arl=Reverse/@RandomChoice@Subsets[EdgeList[t],{m}];
	d= EdgeAdd[t,arl]];

GoodTournament[n_Integer]:=Module[{i,t,subgl},
	Do[t=Tournament[n];
		If[ConnectedGraphQ[#]&&ObstructionFreeQ[#,ObstructionList["Tournament"]]&@t,Return[t]],
		{i,1000}]];

GoodSemiCompleteDigraph[n_Integer,m_Integer:1]/;1<=m<=n (n-1)/2:=Module[{i,d,subgl},
	Do[d=SemiCompleteDigraph[n,m];
		If[ConnectedGraphQ[#]&&ObstructionFreeQ[#,ObstructionList["SemiCompleteDigraph"]]&@d,Return[d]],
		{i,1000}]];

BFSVertexPartition[d_Graph,r_Integer]:=Module[{p,vl,vt,ct,vused},
	vt={r}; ct={}; vused=vt; vl=Complement[VertexList@d,vt];
	p=Reap[While[vl!={},
		vt=Complement[#,vused]&@VertexInComponent[d,vt,1];
		AppendTo[vused,#]&/@vt;
		If[AcyclicGraphQ@Subgraph[d,vt],vt=TopologicalSort@Subgraph[d,vt],ct=FindCycle[Subgraph[d,vt],{2,3},All]];
		Sow@{vt,ct};		
		vl=Complement[vl,vt]; ct={}]][[2,1]];
	Prepend[p,{{r},{}}]];

MaxOutDegreeVertexList[d_Graph]:=Module[{},
	Flatten@Position[#,Max[#]]&@VertexOutDegree@d];

MinInDegreeVertexList[d_Graph]:=Module[{},
	Flatten@Position[#,Min[#]]&@VertexInDegree@d];

BFSVertexPartitionList[d_Graph]:=Module[{},
	BFSVertexPartition[d,#]&/@MaxOutDegreeVertexList@d];

HangingCycleList[d_Graph,v_Integer]:=Module[{vl,c2l,c3l,subg,cbad,td,ind},
	ind={};
	c2l=FindCycle[{d,v},{2},All];
	vl=Intersection[VertexInComponent[d,{v},1],VertexOutComponent[d,{v},1]];
	td=VertexDelete[d,Select[vl,UnsameQ[#,v]&]];
	c3l=FindCycle[{td,v},{3},All];
	subg=Subgraph[td,#]&@Union@Flatten[c3l/.DirectedEdge->List];
	cbad=FindCycle[subg,{2},All];
	If[cbad!={},Do[If[Flatten[Intersection[c3l[[i]],#]&/@cbad]!={},AppendTo[ind,i]],{i,Length@c3l}]];
	Union[c2l,Delete[c3l,List/@ind]]];

PossibleDigraphList[dsupp_Graph]:=Module[{el},
	el=DirectedEdge@@@{#,Reverse@#}&/@EdgeList@GraphComplement@UndirectedGraph@dsupp;
	EdgeAdd[dsupp,#]&/@Tuples[el]];
