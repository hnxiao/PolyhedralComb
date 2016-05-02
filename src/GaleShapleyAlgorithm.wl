(* ::Package:: *)

GaleShapleyAlgorithm[g_Graph,pref_List]:=Module[{vc,cel,cpref,mpref,wpref,candidate,rej},
	If[Not@BipartiteGraphQ[g],Return["Not bipartite graph"]];
	vc=VertexCount@g;
	cel=Sort/@EdgeList@g;
	cpref=Map[Sort,pref,{2}];
	rej=EdgeList@g;
	While[rej!={},
	mpref=Part[cpref,1;;vc/2];
	wpref=Part[cpref,(vc/2+1);;vc];
	candidate=Propose[g,mpref];
	Print@candidate;
	rej=Reject[g,wpref,candidate];
	If[rej=={},Return@candidate];
	Print@rej;
	cpref=UpdatePreference[cpref,rej];
	Print@cpref;]];


Propose[ppref_List]:=First/@ppref;

Reject[rpref_List,prop_List]:=Module[{IncidentQ,MaxPosition,conflicts,subpref,indices},
	IncidentQ[e_,f_]:=IntersectingQ[List@@e,List@@f];
	conflicts =Select[Subsets[prop,{2}],IncidentQ@@#&];
	If[conflicts=={},Return[{}]];
	subpref=Select[rpref,IntersectingQ[#,Flatten@conflicts]&];
	MaxPosition=Max@@Position[#1,Alternatives@@#2]&;
	indices=MaxPosition@@@Gather[Join[subpref,conflicts],IntersectingQ];
	Flatten[Take@@@Transpose[{subpref,List/@indices}]]];

UpdatePreference[pref_List,rej_List]:=Fold[DeleteCases,#,rej]&/@pref;


CompleteBipartiteGraph[i_Integer]:=CompleteGraph[{i,i}]
