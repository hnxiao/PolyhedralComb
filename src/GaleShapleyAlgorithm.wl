(* ::Package:: *)

GaleShapleyAlgorithm[ppref_List,rpref_List]:=Module[{pprefs,rprefs,proposals,rejects},
	If[Not@BipartiteGraphQ[Graph[Flatten@ppref]],Return["Not bipartite graph"]];
	pprefs=Map[Sort,ppref,{2}];
	rprefs=Map[Sort,rpref,{2}];
	rejects=Last/@Select[rprefs,UnsameQ[#,{}]&];
	While[rejects!={},
	proposals=Propose[pprefs]; Print@proposals;
	rejects=Reject[rprefs,proposals]; Print@rejects;
	{pprefs,rprefs}=UpdatePreference[pprefs,rprefs,rejects]];
	proposals];


Propose[ppref_List]:=First/@Select[ppref,UnsameQ[#,{}]&];

Reject[rpref_List,prop_List]:=Module[{conflicts,Rejects},
	conflicts=Select[IncidenceList[Graph@prop,#]&/@VertexList[Graph@prop],Length[#]>1&];
	If[conflicts=={},Return[{}]];
	Rejects[l_,subl_]:=DeleteCases[subl,_?(SameQ[Position[l,#][[1]][[1]],Min@@Flatten@@{Position[l,#]&/@subl}]&)];
	Flatten[Rejects@@@Select[Gather[Join[rpref,conflicts],IntersectingQ],Length[#]>1&]]];
(*
Reject[rpref_List,prop_List]:=Module[{subg,conflicts,subpref,ListPosition,conflictindices},
	subg=Graph[prop];
	conflicts=Select[IncidenceList[subg,#]&/@VertexList[subg],Length[#]>1&];
	If[conflicts=={},Return[{}]];
	subpref=Select[rpref,IntersectingQ[#,Flatten@conflicts]&];
	ListPosition=Flatten@Position[#1,Alternatives@@#2]&;
	conflictindices=ListPosition@@@Gather[Join[subpref,conflicts],IntersectingQ];
	Flatten[Part@@@Transpose@Join[{subpref},{Drop[#,1]&/@Sort/@conflictindices}]]];
*)
UpdatePreference[ppref_List,rpref_List,rej_List]:=Map[Fold[DeleteCases,#,rej]&,{ppref,rpref},{2}];


CompleteBipartitePreferenceSystem[i_Integer]:=Module[{g,pref,ppref,rpref},
	g=CompleteGraph[{i,i}];
	pref=PreferenceList@g;
	{ppref,rpref}={pref[[1;;i]],pref[[i+1;;2i]]}];
