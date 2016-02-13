(* ::Package:: *)

BeginPackage["Kernels`",{"Graphs`"}]


KernelExistsQ::usage="KernelExistsQ[g] yields True if g has a kernel and False otherwise.";
FindKernel::usage="FindKernel[g] returns all kernels of g.";
(*
FindKernel::usage=
	"FindKernel[g] returns a random kernel of g.\n"<>
	"FindKernel[g,"All"] returns all kernels of g.";
*)
FractionalKernelExistsQ::usage="FractionalKernelExistsQ[g] yields True if g has a FRACTIONAL kernel and False otherwise.";
FindFractionalKernel::usage="FindFrKernel[g] returns all fractional kernels of g in incidence vectors.";
CriticalKernelImperfectQ::usage="CriticalKernelImperfectQ[g] yields True if g is critical kernel imperfect (CKI) and False otherwise.";
CliqueAcyclicQ::usage="CliqueAcyclicQ[g] yields True if every clique of g has a kernel and False otherwise.";
OddCycleChordExistsQ::usage="OddCycleChordExistQ[g] yields True if every directed cycle has a (pseudo-)chord and False otherwise.";


Begin["`Private`"]


KernelExistsQ[g_Graph]:=Module[{pkl},
	pkl=FindIndependentVertexSet[g,{1,Length@VertexList[g]},All];
	Apply[Or,DominatingVertexSetQ[g,#]&/@pkl]];

FindKernel[g_Graph]:=Module[{pkl},
	pkl=FindIndependentVertexSet[g,{1,Length@VertexList[g]},All];
	Select[pkl,DominatingVertexSetQ[g,#]&]];

FractionalKernelExistsQ[g_Graph]:=Module[{},
	UnsameQ[Complement[Union@Flatten@FindFractionalKernel[g],{0,1}],{}]];

FindFractionalKernel[g_Graph]:=Module[{A1,A2,A3,A,b},
	A1=-DominationMatrix@g;
	A2=StabilityMatrix@g;
	A3=-IdentityMatrix[VertexCount@g];
	A=Join[A1,A2,A3];
	b=Join[ConstantArray[-1,Length@A1],ConstantArray[1,Length@A2],ConstantArray[0,VertexCount@g]];
	VertexEnumeration[A,b]];

CriticalKernelImperfectQ[g_Graph]:=Module[{vl,subvl,subgl},
	vl=VertexList@g;
	subvl=Subsets[vl,{3,Length@vl-1}];
	subgl=Subgraph[g,#]&/@subvl;
	Not@KernelExistsQ[g]&&Apply[And,KernelExistsQ/@subgl]];

CliqueAcyclicQ[g_Graph]:=Module[{cl,gl,obst},
	cl=FindClique[UndirectedGraph@g,Length@VertexList[g],All];
	gl=Subgraph[g,#]&/@cl;
	(*obst: minimum CKI cliques, which can be obtained from a directed cycle by adding opposite arcs to nonadjacent vertices*)
	obst={Graph[{1, 2, 3}, {{{1, 2}, {2, 3}, {3, 1}}, Null}, {FormatType -> TraditionalForm, GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]], FormatType -> TraditionalForm, GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]]}],Graph[{1, 2, 3, 4}, {{{1, 2}, {1, 3}, {3, 1}, {4, 1}, {2, 3}, {2, 4}, {4, 2}, {3, 4}}, Null}, {FormatType -> TraditionalForm, GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]], FormatType -> TraditionalForm, GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]]}],Graph[{1, 2, 3, 4, 5}, {{{1, 2}, {3, 1}, {1, 4}, {4, 1}, {1, 5}, {5, 1}, {2, 3}, {3, 2}, {2, 4}, {2, 5}, {5, 2}, {3, 4}, {4, 3}, {5, 3}, {4, 5}}, Null}, {FormatType -> TraditionalForm, GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]], FormatType -> TraditionalForm, GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]]}],Graph[{1, 2, 3, 4, 5, 6}, {{{1, 2}, {3, 1}, {1, 4}, {4, 1}, {1, 5}, {5, 1}, {1, 6}, {6, 1}, {2, 3}, {3, 2}, {2, 4}, {2, 5}, {5, 2}, {2, 6}, {6, 2}, {3, 4}, {4, 3}, {5, 3}, {3, 6}, {6, 3}, {4, 5}, {5, 4}, {4, 6}, {6, 5}}, Null}, {FormatType -> TraditionalForm, GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]], FormatType -> TraditionalForm, GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]]}],Graph[{1, 2, 3, 4, 5, 6, 7}, {{{1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 7}, {7, 1}, {1, 3}, {3, 1}, {1, 4}, {4, 1}, {1, 5}, {5, 1}, {1, 6}, {6, 1}, {2, 4}, {4, 2}, {2, 5}, {5, 2}, {2, 6}, {6, 2}, {2, 7}, {7, 2}, {3, 5}, {5, 3}, {3, 6}, {6, 3}, {3, 7}, {7, 3}, {4, 6}, {6, 4}, {4, 7}, {7, 4}, {5, 7}, {7, 5}}, Null}, {FormatType -> TraditionalForm, GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]], FormatType -> TraditionalForm, GraphLayout -> {"Dimension" -> 2}, GridLinesStyle -> Directive[GrayLevel[0.5, 0.4]], VertexLabels -> {None}}]};
	If[Apply[And,KernelExistsQ/@gl],ObstructionFreeQ[g,obst],False]];

OddCycleChordExistsQ[g_Graph]:=Module[{cyclel},
	cyclel=Flatten[FindCycle[g,{#},All]&/@Select[VertexList@g,OddQ],1];
	Return@Apply[And,ChordExistsQ[g,#]&/@cyclel]];


(* Private functions *)
DominationMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,VertexOutComponent[g,{#},1]&/@VertexList[g],VertexList@g,1]];

StabilityMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,FindClique[UndirectedGraph@g,Infinity,All],VertexList@g,1]];

DominatingVertexSetQ[g_Graph,vl_List]:=Module[{},
	Sort@VertexInComponent[g,vl,1]==Sort@VertexList[g]];

ChordExistsQ::usage="ChordExistsQ[g,el] yields True if the directed cycle consisting of el has a (pseudo-)chord and False otherwise.";
ChordExistsQ[g_Graph,el_List]:=Module[{vl,vpl,pl,chordlist},
	vl=VertexList@Subgraph[g,el];
	vpl=Subsets[vl,{2}];
	pl=Union[DirectedEdge@@@vpl,Reverse/@DirectedEdge@@@vpl];
	chordlist=Complement[pl,el];
	Return@Apply[Or,EdgeQ[g,#]&/@chordlist]];


End[]


EndPackage[]
