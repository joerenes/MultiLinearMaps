(* ::Package:: *)

(* ::Subsubsection:: *)
(*Prologue*)


BeginPackage["MultiLinearMaps`"];


Unprotect[MapDict,System,AtomicSpace,VecSpace,IndexDict,MultiMap];
ClearAll[MapDict,System,AtomicSpace,VecSpace,IndexDict,MultiMap];
Unprotect[ValidMapQ,MapEqualQ,ComposableQ,AtomicQ,ContractableQ];
ClearAll[ValidMapQ,MapEqualQ,ComposableQ,AtomicQ,ContractableQ];
Unprotect[SystemMap,ComposeMaps,AddMaps,PartialTrace,MapTranspose,Adjoint,PartialTranspose,ToMatrix,LazyAdd];
ClearAll[SystemMap,ComposeMaps,AddMaps,PartialTrace,MapTranspose,Adjoint,PartialTranspose,ToMatrix,LazyAdd];
Unprotect[BasisElement,BasisKet,BasisBra,BasisProj,IdentityOp,OmegaKet,OmegaBra,OmegaOp,SwapOp,FromMatrix];
ClearAll[BasisElement,BasisKet,BasisBra,BasisProj,IdentityOp,OmegaKet,OmegaBra,OmegaOp,SwapOp,FromMatrix];


(* ::Text:: *)
(*Usage messages*)


ComposeMaps::usage="ComposeMaps[M1,M2,...,Method->method] returns the composition M1 \[EmptySmallCircle] M2 \[EmptySmallCircle] \[CenterEllipsis]. Accessible by the infix notation M1 ** M2.\n     Additionally, there are two internal methods of computing the composition, available as \"Dot\" and \"TensorContract\". The former is the default as it appears to be faster.";
PartialTranspose::usage="PartialTranspose[M,syslist] returns the partial transpose of M with respect to the systems in syslist.";
PartialTrace::usage="PartialTrace[M,syslist] returns the partial trace of M with respect to the systems in syslist. If no systems are explicitly given, all systems that can be traced out are. An empty list {} will return the input map.";
MapTranspose::usage="MapTranspose[M] returns the transpose of M. Available as Transpose.";
Adjoint::usage="Adjoint[M] returns the adjoint of M.";
SystemMap::usage="SystemMapping[M] returns the dictionary of the map, which is a list of (the names of) output systems and a list of input systems, together under the head MapDict.";
AddMaps::usage="AddMaps[M1,M2] returns the sum of the two maps. Accessible infix as M1 + M2.";
ToMatrix::usage="ToMatrix[M,sortinglist] returns the matrix representation of M, with tensor subsystems ordered according to sortinglist.";
FromMatrix::usage="FromMatrix[out,in,m] returns a MultiMap object which maps the systems in the list in to those in out according to the matrix m. If only one list of systems is given, the map takes these systems to themselves.";
BasisBra::usage="BasisBra[sys_System,k_Integer] returns the kth basis bra of system sys.";
BasisKet::usage="BasisKet[sys,k] returns the kth basis ket of system sys.";
BasisProj::usage="BasisProj[sys,k] returns the projector onth the kth basis element of system sys.";
IdentityOp::usage="IdentityOp[syslist] returns the identity operator on the systems in syslist.\nIdentityOp[outlist,inlist] gives the identity operator from the inlist to the outlist systems. Note that the latter map is basis dependent and uses the standard basis.";
OmegaOp::usage="OmegaOp[sys1,sys2] returns the projector onto the canonical maximally entangled state of systems sys1 and sys2.";
OmegaKet::usage="OmegaKet[sys1,sys2] returns the ket corresponding to the unnormalized maximally entangled state of systems sys1 and sys2.";
OmegaBra::usage="OmegaKet[sys1,sys2] returns the bra corresponding to the unnormalized maximally entangled state of systems sys1 and sys2.";
LazyAdd::usage="LazyAdd[M1,M2] returns the sum of the two maps, provided they are compatible, i.e. if, by including suitable identity mappings, they can be made to both represent the same kind of map. Available infix as \!\(\*SubscriptBox[\(+\), \(1\)]\).";
SwapOp::usage="SwapOp[sys1,sys2] returns the swap operator of the two systems. Input System objects.";
MapDict::usage="MapDict[codomain,domain] represents the codomain and domain of a linear map.";
System::usage="System[name,dimension] represents a named vector space of given dimension.";
AtomicSpace::usage="AtomicSpace[system,type] represents the system as either an input (bra) or output (ket) space.";
VecSpace::usage="VecSpace[atom1,atom2,...] represents the tensor product of a sequence of atomic spaces.";
IndexDict::usage="IndexDict[vecspace1,vecspace2,...] records which vector spaces are associated to which indices in a tensor.";
MultiMap::usage="MultiMap[index,tensor] represents a linear map as a tensor (as a SparseArray) and an IndexDict.";


Begin["`Private`"];


(* ::Text:: *)
(*Data types:*)
(*MapDict: list of output and input systems. Elements of the lists "should" be strings, but this isn't enforced. The convention is "output" given "input".*)
(*System: name and dimension of a system. Name should be a string, dimension a positive integer. Whether dimension 1 works is a good question.*)
(*AtomicSpace: a System and a type, which is either the string "ket" or "bra", indicating the system is an output or input, respectively.*)
(*VecSpace: a list of AtomicSpaces, representing their tensor product.*)
(*IndexDict: a list of VecSpaces, identifying which indices of a tensor correspond to which VecSpaces.*)
(*MultiMap: an IndexDict and a tensor, representing a linear transformation. *)


(* ::Subsubsection:: *)
(*MapDict *)


(* ::Text:: *)
(*MapDict names the domain and codomain systems of a map. It has two elements: a list of codomain systems (output) and a list of domain systems (input). The convention is easy to remember as "output given input". *)
(**)
(*Check validity of MapDict, equality of two of them.*)


ValidMapQ[x_MapDict]:=And@@(DuplicateFreeQ/@x);
MapEqualQ[x_MapDict,y_MapDict]:=Equal@@((Sort/@#&/@{List@@x,List@@y}));
Equal[MapDict[oL_,iL_],MapDict[oR_,iR_]]^:=MapEqualQ[MapDict[oL,iL],MapDict[oR,iR]]


(* ::Text:: *)
(*Functions related to the composition of two maps.*)


MapDict::multiplearg = "`1` in argument `2` does not represent a valid linear map.";
chkArgs[L_MapDict,R_MapDict]:=If[
	ValidMapQ[L],
	If[
		ValidMapQ[R],
		True,
		False;Message[MapDict::multiplearg,R,2]
	],
	False;Message[MapDict::multiplearg,L,1]
];

CompositionSystems[L_MapDict,R_MapDict]/;chkArgs[L,R]:=Intersection[L[[2]],R[[1]]];

rawComposeMaps[L_MapDict,R_MapDict]:=With[
	{inner=CompositionSystems[L,R]},
	MapDict@@({Join[L[[1]],Complement[R[[1]],#]],Join[R[[2]],Complement[L[[2]],#]]}&[inner])
];

ComposableQ[L_MapDict,R_MapDict]/;chkArgs[L,R]:=ValidMapQ[rawComposeMaps[L,R]];

ComposeMaps::inputs = "Input maps are not composable in this order.";
ComposeMaps[L_MapDict,R_MapDict]/;chkArgs[L,R]:=With[
	{cmp=rawComposeMaps[L,R]},
	If[
		ValidMapQ[cmp],
		cmp,
		Message[ComposeMaps::inputs]
	]
];
NonCommutativeMultiply[MapDict[oL_,iL_],MapDict[oR_,iR_]]^:=ComposeMaps[MapDict[oL,iL],MapDict[oR,iR]]


(* ::Text:: *)
(*Functions for contraction of a map.*)


MapDict::singlearg = "`1` does not represent a valid linear map.";
chkArgs[x_MapDict]:=If[
	ValidMapQ[x],
	True,
	Message[MapDict::singlearg,x];False
];
	
ContractableSystems[x_MapDict]/;chkArgs[x]:=Intersection[x[[1]],x[[2]]];
ContractableQ[x_MapDict,sysnames_List]:=And@@(SubsetQ[#,sysnames]&/@x);
ContractableQ[x_MapDict,sysname_]:=ContractableQ[x,{sysname}];


(* ::Subsubsection:: *)
(*System / AtomicSpace / VecSpace*)


(* ::Text:: *)
(*System represents an individual input or output space of a map. It has two components: first the name of the system and second its dimension.*)


Name[x_System]:=x[[1]];
Dimension[x_System]:=x[[2]];
ValidSystemQ[x_System]:=StringQ[Name[x]]&&With[{d=Dimension[x]},IntegerQ[d]&&Positive[d]];


(* ::Text:: *)
(*AtomicSpace represents a system along with a type, bra or ket, that denotes whether the system is an input or output, respectively. *)


Name[x_AtomicSpace]:=Name[x[[1]]]
Dimension[x_AtomicSpace]:=Dimension[x[[1]]];
Type[x_AtomicSpace]:=x[[2]];


(* ::Text:: *)
(*VecSpace is a collection of AtomicSpaces, for the purposes of representing their tensor product.*)


AtomicQ[x_VecSpace]:=Length[x]==1;
Dimension[x_VecSpace]:=Times@@(Level[x,{3}][[2;;;;2]]); 


(* ::Subsubsection:: *)
(*IndexDict / MultiMap*)


(* ::Text:: *)
(*Simple functions and manipulation of IndexDicts*)


AtomicQ[x_IndexDict]:=And@@AtomicQ/@x;
Atoms[x_IndexDict]:=Level[x,{2}];
DimensionList[x_IndexDict]:=List@@(Dimension/@x);


Kets[x_IndexDict]:=Select[Atoms[x],#[[2]]=="ket"&];
Bras[x_IndexDict]:=Select[Atoms[x],#[[2]]=="bra"&];
SystemMap[x_IndexDict]:=MapDict@@(Map[Name,{Kets[x],Bras[x]},{2}]);
KetIndices[x_IndexDict]:=Flatten[Position[Atoms[x],z_/;Type[z]=="ket"]];
BraIndices[x_IndexDict]:=Flatten[Position[Atoms[x],z_/;Type[z]=="bra"]];
KetAddress[x_IndexDict,sysname_]:=Position[x,z_/;Name[z]==sysname&&Type[z]=="ket",{2}];
BraAddress[x_IndexDict,sysname_]:=Position[x,z_/;Name[z]==sysname&&Type[z]=="bra",{2}]
KetAddresses[x_IndexDict,sysnames_List]:=Position[x,z_/;MemberQ[sysnames,Name[z]]&&Type[z]=="ket",{2}];
BraAddresses[x_IndexDict,sysnames_List]:=Position[x,z_/;MemberQ[sysnames,Name[z]]&&Type[z]=="bra",{2}];
KetAddresses[x_IndexDict]:=Position[x,z_/;Type[z]=="ket",{2}];
BraAddresses[x_IndexDict]:=Position[x,z_/;Type[z]=="bra",{2}]


(* ::Text:: *)
(*Simple MultiMap functions*)


SystemMap[t_MultiMap]:=SystemMap[t[[1]]];
ValidMapQ[t_MultiMap]:=And[ValidMapQ@SystemMap@t,DimensionList[t[[1]]]==Dimensions[t[[2]]]];
ComposableQ[L_MultiMap,R_MultiMap]:=ComposableQ[SystemMap@L,SystemMap@R];
ContractableQ[t_MultiMap,sysnames_List]:=ContractableQ[SystemMap[t],sysnames];
ContractableQ[t_MultiMap,sysname_]:=ContractableQ[SystemMap[t],{sysname}];
SystemMapEqualQ[t1_MultiMap,t2_MultiMap]:=SystemMap[t1]==SystemMap[t2]; 
AtomicQ[t_MultiMap]:=And[AtomicQ[t[[1]]],List@@Dimension/@Atoms[t[[1]]]==Dimensions[t[[2]]]]


Times[MultiMap[x_,y_],z_?NumericQ]^:=MultiMap[x,z y];


(* ::Subsubsection::Closed:: *)
(*Constructors*)


BasisElement::dim="Requested element must be an integer between 0 and `1`"; 
BasisElement[sys_System,num_Integer,type_]/;
If[
	num<Dimension[sys]&&num>=0,
	True,
	Message[BasisElement::dim,Dimension[sys]-1];False
]:=MultiMap@@{IndexDict[VecSpace[AtomicSpace[sys,type]]],SparseArray[{num+1->1},{Dimension[sys]}]};
BasisKet[sys_System,num_Integer]:=BasisElement[sys,num,"ket"];
BasisBra[sys_System,num_Integer]:=BasisElement[sys,num,"bra"];
BasisProj[sys_System,num_Integer]:=BasisKet[sys,num]**BasisBra[sys,num]


SpId[d_]:=SparseArray[{{i_,i_}->1},{d,d}];


IdentityOp[out_List,in_List]:=MultiMap[IndexDict[VecSpace@@(AtomicSpace[#,"ket"]&/@out),VecSpace@@(AtomicSpace[#,"bra"]&/@in)],SpId[Times@@(Dimension/@in)]]
IdentityOp[systems_List]:=MultiMap[IndexDict[VecSpace@@(AtomicSpace[#,"ket"]&/@systems),VecSpace@@(AtomicSpace[#,"bra"]&/@systems)],SpId[Times@@(Dimension/@systems)]];
IdentityOp[sys_System]:=IdentityOp[{sys}];


dimstr="Input systems do not have the same dimension.";
OmegaKet::inputdim=dimstr;
OmegaBra::inputdim=dimstr;
OmegaOp::inputdim=dimstr;
SwapOp::inputdim=dimstr;

chkDim[s1_System,s2_System,f_]:=If[
	Dimension[s1]==Dimension[s2],
	True,
	Message[f::inputdim];False
];
OmegaKet[sys1_System,sys2_System]/;chkDim[sys1,sys2,OmegaKet]:=
MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"ket"]],VecSpace[AtomicSpace[sys2,"ket"]]],SpId[Dimension@sys1]];
OmegaBra[sys1_System,sys2_System]/;chkDim[sys1,sys2,OmegaBra]:=
MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"bra"]],VecSpace[AtomicSpace[sys2,"bra"]]],SpId[Dimension@sys1]];
OmegaOp[sys1_System,sys2_System]/;chkDim[sys1,sys2,OmegaOp]:=MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"ket"],AtomicSpace[sys1,"bra"]],VecSpace[AtomicSpace[sys2,"ket"],AtomicSpace[sys2,"bra"]]],SpId[(Dimension@sys1)^2]];
SwapOp[sys1_System,sys2_System]/;chkDim[sys1,sys2,SwapOp]:=MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"bra"],AtomicSpace[sys1,"ket"]],VecSpace[AtomicSpace[sys2,"ket"],AtomicSpace[sys2,"bra"]]],SpId[(Dimension@sys1)^2]];





FromMatrix::dim="Dimensions of the input matrix do not match those of the input systems.";
FromMatrix[sysout_List,sysin_List,matrix_]/;
And[
	chkArgs[MapDict[Name/@sysout,Name/@sysin]],
	If[
		{Times@@(Dimension/@sysout),Times@@(Dimension/@sysin)}==Dimensions[matrix],
		True,
		Message[FromMatrix::dim];False
	]
]:=
MultiMap[IndexDict[VecSpace@@(AtomicSpace[#,"ket"]&/@sysout),VecSpace@@(AtomicSpace[#,"bra"]&/@sysin)],SparseArray@matrix]
FromMatrix[systems_List,matrix_]:=FromMatrix[systems,systems,matrix];


(* ::Subsubsection:: *)
(*Composition*)


(* ::Text:: *)
(*we're going to need to work with atomic tensors in which each index refers to an AtomicSpace.*)


Atomize[x_IndexDict]:=IndexDict@@(VecSpace[#]&)/@Atoms[x];
Atomize[t_MultiMap]:=If[
	AtomicQ[t],
	t,
	With[
		{atomdict=Atomize[t[[1]]]},
		MultiMap@@{atomdict,ArrayReshape[t[[2]],List@@Dimension/@atomdict]}
	]
];


(* ::Text:: *)
(*For manipulating the IndexDict, assume it is atomic.*)


CompositionSystems[L_IndexDict,R_IndexDict]:=CompositionSystems[SystemMap@L,SystemMap@R];
CompositionIndices[L_IndexDict,R_IndexDict]:=With[
	{inner=CompositionSystems[L,R]},
	Flatten[{Position[Atoms@L,z_/;Type[z]=="bra"&&Name[z]==#],Position[Atoms@R,z_/;Type[z]=="ket"&&Name[z]==#]}]&/@(inner)
];
(* return the index pairs, one each from left and right, \.7f\.7f\.7fthat need to be contracted in order to compose the two maps *)
ComposeMaps[L_IndexDict,R_IndexDict]:=With[
	{ci=CompositionIndices[L,R]},
	If[
		ci=={},
		IndexDict@@(Join[L,R]),
		IndexDict@@(Join@@MapThread[Delete,{{L,R},Transpose[{#}]&/@Transpose[ci]}])
	]
];

ComposeAtomicTensors[L_MultiMap,R_MultiMap]/;If[
	ComposableQ[L,R],
	True,
	Message[ComposeMaps::inputs];False
]:=MultiMap@@{ComposeMaps[L[[1]],R[[1]]],Activate[TensorContract[Inactive[TensorProduct][L[[2]],R[[2]]],(#+{0,Length[L[[1]]]})&/@CompositionIndices[L[[1]],R[[1]]]]]};
ComposeMapsTC[L_MultiMap,R_MultiMap]:=ComposeAtomicTensors[Atomize[L],Atomize[R]];
ComposeMapsTC[x_MultiMap]:=x;
ComposeMapsTC[L_MultiMap,R_MultiMap,x__MultiMap]:=ComposeMapsTC[ComposeMapsTC[L,R],ComposeMapsTC[x]];


CompositionIndicesDot[L_IndexDict,R_IndexDict]:=With[
	{cilist=CompositionIndices[L,R]},
	If[
		cilist=={},
		{{Range[Length[Atoms@L]],{}},{{},Range[Length[Atoms@R]]}},
		{{Complement[Range[Length[Atoms@L]],cilist[[;;,1]]],cilist[[;;,1]]},{cilist[[;;,2]],Complement[Range[Length[Atoms@R]],cilist[[;;,2]]]}}
	]
];

(*ComposeMapsDot[L_MultiMap,R_MultiMap]/;If[
	ComposableQ[L,R],True,Message[ComposeMaps::inputs];False
]:=Module[
	{ci=CompositionIndicesDot[L[[1]],R[[1]]],id},
	id=IndexDict[VecSpace@@(Atoms[L[[1]]][[ci[[1,1]]]]),VecSpace@@(Atoms[R[[1]]][[ci[[2,2]]]])];
	If[
		ci[[1,2]]\[Equal]{},
		MultiMap[id,SparseArray[Transpose[{Flatten[Atomize[L][[2]]]}]].SparseArray[{Flatten[Atomize[R][[2]]]}]],
		MultiMap[id,SparseArray[Flatten[Atomize[L][[2]],ci[[1]]]].SparseArray[Flatten[Atomize[R][[2]],ci[[2]]]]]
	]
];*)
ComposeMapsDot[L_MultiMap,R_MultiMap]/;If[
	ComposableQ[L,R],
	True,
	Message[ComposeMaps::inputs];False
]:=Module[
	{ci=CompositionIndicesDot[L[[1]],R[[1]]],id},
	id=IndexDict[VecSpace@@(Atoms[L[[1]]][[ci[[1,1]]]]),VecSpace@@(Atoms[R[[1]]][[ci[[2,2]]]])];
	If[
		ci[[1,2]]=={},
		MultiMap[id,SparseArray[Transpose[{Flatten[Atomize[L][[2]]]}]].SparseArray[{Flatten[Atomize[R][[2]]]}]],
		ci=DeleteCases[ci,{},{2}];
		MultiMap[id,SparseArray[Flatten[Atomize[L][[2]],ci[[1]]]].SparseArray[Flatten[Atomize[R][[2]],ci[[2]]]]]
	]
];
ComposeMapsDot[x_MultiMap]:=x;
ComposeMapsDot[L_MultiMap,R_MultiMap,x__MultiMap]:=ComposeMapsDot[ComposeMapsDot[L,R],ComposeMapsDot[x]];


Options[ComposeMaps]={Method->"Dot"};
ComposeMaps[x_MultiMap,opts:OptionsPattern[]]:=x;
ComposeMaps[L_MultiMap,R_MultiMap,opts:OptionsPattern[]]:=If[
	OptionValue[Method]=="TensorContract",
	ComposeMapsTC[L,R],
	ComposeMapsDot[L,R]
];
ComposeMaps[L_MultiMap,R_MultiMap,x__MultiMap,opts:OptionsPattern[]]:=If[
	OptionValue[Method]=="TensorContract",
	ComposeMapsTC[L,R,x],
	ComposeMapsDot[L,R,x]
]
NonCommutativeMultiply[MultiMap[x1_,x2_],MultiMap[y1_,y2_]]^:=ComposeMaps[MultiMap[x1,x2],MultiMap[y1,y2]];


(* ::Subsubsection:: *)
(*Contraction (partial trace)*)


(* ::Text:: *)
(*Assume the systems can be contracted; error handling in the PartialTrace function.*)


ContractionIndices[x_IndexDict,sysnames_List]:=
With[
	{atoms=Atoms[x]},
	Flatten[{Position[atoms,z_/;Type[z]=="bra"&&Name[z]==#],Position[atoms,z_/;Type[z]=="ket"&&Name[z]==#]}]&/@(sysnames)
];


ContractMap[x_IndexDict,sysnames_List]:=With[
	{r=Select[Atoms[x],!MemberQ[sysnames,Name[#]]&]},
	If[
		r=={},
		IndexDict[],
		IndexDict[Sequence@@(VecSpace[#]&/@r)]
	]
]


(* ::Text:: *)
(*Partial Trace*)


PartialTrace[x_MultiMap,systems_List:"all"]/;If[
	StringQ[systems]||ContractableQ[x,Name/@systems],
	True,
	Message[PartialTrace::inputs];False
]:=With[
	{sysnames=If[
		StringQ[systems],
		ContractableSystems[SystemMap[x]],
		Name/@systems
	]},
	MultiMap[ContractMap[#[[1]],sysnames],TensorContract[#[[2]],ContractionIndices[#[[1]],sysnames]]]&[Atomize[x]]
];
PartialTrace[x_MultiMap,s_System]:=PartialTrace[x,{s}];
Tr[MultiMap[x1_,x2_]]^:=PartialTrace[MultiMap[x1,x2]];


(* ::Subsubsection:: *)
(*Addition / system ordering*)


NameSort[x_IndexDict/;AtomicQ[x]]:=IndexDict@@(VecSpace[#]&/@SortBy[Level[x,{2}],{Name,Type[#]=="bra"&}])
TypeSort[x_IndexDict/;AtomicQ[x]]:=IndexDict@@(VecSpace[#]&/@SortBy[Level[x,{2}],{Type[#]=="bra"&,Name}]);
OwnSort[x_IndexDict/;AtomicQ[x],names_List]:=IndexDict@@(VecSpace[#]&/@SortBy[Level[x,{2}],{Type[#]=="bra"&,Position[names,Name[#]][[1,1]]&}])
(* this last one sorts by type and then by name according to a given list of names *)


genPerm[list1_,list2_]:=Flatten[Position[list1,#]&/@list2];
SortMap[x_IndexDict/;AtomicQ[x],f_]:=genPerm[List@@(f[x]),List@@x];


Canonicalize[t_MultiMap,sortlist_List:{}]:=
If[
	Length[t[[1]]]==0,
	t,
	With[
		{sortingf=If[sortlist=={},TypeSort,OwnSort[#,sortlist]&]},
		MultiMap@@{sortingf[#[[1]]],Transpose[#[[2]],SortMap[#[[1]],sortingf]]}&[Atomize[t]]
	]
];
Canonicalize1[t_MultiMap,sortlist_List:{}]:=
If[
	Length[t[[1]]]==0,
	t,
	Module[{sortingf},
		If[sortlist=={},sortingf=TypeSort,sortingf=OwnSort[#,sortlist]&];
		MultiMap@@{sortingf[#[[1]]],Transpose[#[[2]],SortMap[#[[1]],sortingf]]}&[Atomize[t]]
	]
];


MapEqualQ[x_MultiMap,y_MultiMap]:=
With[
	{xc=Canonicalize[x],yc=Canonicalize[y]},
	SystemMapEqualQ[xc,yc]&&(xc[[2]]==yc[[2]])
];
Equal[MultiMap[oL_,iL_],MultiMap[oR_,iR_]]^:=MapEqualQ[MultiMap[oL,iL],MultiMap[oR,iR]]


AddMaps::input="Maps with differing input and output spaces cannot be added.";
AddMaps[t1_MultiMap,t2_MultiMap]/;
If[
	SystemMapEqualQ[t1,t2],
	True,
	Message[AddMaps::input];False]:=
With[
	{ct1=Canonicalize[t1]},
	MultiMap[ct1[[1]],ct1[[2]]+Canonicalize[t2][[2]]]
];
Plus[MultiMap[x1_,y1_],MultiMap[x2_,y2_]]^:=AddMaps[MultiMap[x1,y1],MultiMap[x2,y2]];


MapDifferences[m1_MapDict,m2_MapDict]:=
With[
	{int={Intersection[m1[[2]],m2[[2]]],Intersection[m1[[1]],m2[[1]]]}},
	{Sort[{Complement[m2[[2]],int[[2]]],Complement[m2[[1]],int[[1]]]}],Sort[{Complement[m1[[2]],int[[2]]],Complement[m1[[1]],int[[1]]]}]}
];
CompatibleQ[m1_MapDict,m2_MapDict]:=And@@(#[[1]]==#[[2]]&/@MapDifferences[m1,m2]);
SystemsByName[x_IndexDict,namelist_List]:=Select[Union[#[[1]]&/@Level[x,{2}]],MemberQ[namelist,Name[#]]&];
LazyAdd::incomp="Maps with incompatible input and output spaces cannot be added.";
LazyAdd[t1_MultiMap,t2_MultiMap]/;
If[
	CompatibleQ[SystemMap@t1,SystemMap@t2],
	True,
	Message[LazyAdd::incomp]
]:=Module[
	{e1,e2,diffs=#[[1]]&/@MapDifferences[SystemMap[t1],SystemMap[t2]]},
	e1=Canonicalize[t1**IdentityOp[SystemsByName[t2[[1]],diffs[[1]]]]];
	e2=Canonicalize[t2**IdentityOp[SystemsByName[t1[[1]],diffs[[2]]]]];
	MultiMap[e1[[1]],e1[[2]]+e2[[2]]]
];


Matrixize[t_MultiMap,sortlist_:{}]:=
Module[
	{ct,keti,brai},
	ct=Canonicalize[t,sortlist];
	keti=KetIndices[ct[[1]]];
	brai=BraIndices[ct[[1]]];
	Which[
		keti=={}&&brai=={},
		MultiMap[IndexDict[],ct[[2]]],
		keti=={}||brai=={},
		MultiMap[IndexDict[VecSpace@@Atoms[ct[[1]]]],Flatten[ct[[2]]]],
		True,
		MultiMap@@({IndexDict@@(VecSpace@@#&/@SplitBy[Atoms[ct[[1]]],Type]),Flatten[ct[[2]],{keti,brai}]})
	]
]
(* here we need conditional logic to handle scalars, vectors, and operators differently *)


ToMatrix2[t_MultiMap,sortlist_:{}]:=Matrixize[t,sortlist][[2]];
ToMatrix[t_MultiMap,sortlist_:{}]:=With[
	{sm=SystemMap@t,mat=Matrixize[t,sortlist][[2]]},
	Which[
		sm[[1]]=={}&&sm[[2]]=={},
		mat,
		sm[[1]]=={},
		{mat},
		sm[[2]]=={},
		Transpose[{mat}],
		True,
		mat
	]
];


(* ::Subsubsection::Closed:: *)
(*Maps on MultiLinearMaps*)


(* ::Text:: *)
(*Partial Transpose*)


PartialTranspose[x_IndexDict,systems_List]:=
With[
	{sysnames=Name/@systems},
	Module[
		{k=Join[#,{2}]&/@KetAddresses[x,sysnames],b=Join[#,{2}]&/@BraAddresses[x,sysnames]},
		ReplacePart[x,{k->"bra",b->"ket"}]
	]
];
PartialTranspose::inputs = "Systems `1` of the mapping `2` cannot be transposed.";
PartialTranspose[x_MultiMap,systems_List]/;
If[
	ContractableQ[x,Name/@systems],
	True,
	Message[PartialTranspose::inputs,Name/@systems,SystemMap@x];False
]:=
	MultiMap[PartialTranspose[x[[1]],systems],x[[2]]
];
PartialTranspose[x_MultiMap,s_System]:=PartialTranspose[x,{s}];


(* ::Text:: *)
(*Transpose, Adjoint*)


MapTranspose[x_MultiMap]:=MultiMap[Module[{k=Join[#,{2}]&/@KetAddresses[x[[1]]],b=Join[#,{2}]&/@BraAddresses[x[[1]]]},
	ReplacePart[x[[1]],{k->"bra",b->"ket"}]],x[[2]]];
Transpose[MultiMap[x_,y_]]^:=MapTranspose[MultiMap[x,y]]


Adjoint[x_MultiMap]:=
MultiMap[Module[{k=Join[#,{2}]&/@KetAddresses[x[[1]]],b=Join[#,{2}]&/@BraAddresses[x[[1]]]},
	ReplacePart[x[[1]],{k->"bra",b->"ket"}]],Conjugate[x[[2]]]];


(* ::Subsubsection:: *)
(*Epilogue*)


End[]

Protect[MapDict,System,AtomicSpace,VecSpace,IndexDict,MultiMap];
Protect[ValidMapQ,MapEqualQ,ComposableQ,AtomicQ,ContractableQ];
Protect[SystemMap,ComposeMaps,AddMaps,PartialTrace,MapTranspose,Adjoint,PartialTranspose,ToMatrix,LazyAdd];
Protect[BasisElement,BasisKet,BasisBra,BasisProj,IdentityOp,OmegaKet,OmegaBra,OmegaOp,SwapOp,FromMatrix];


Notation`AutoLoadNotationPalette = False;
Needs["Notation`"];
InfixNotation[ParsedBoxWrapper[SubscriptBox["+", "1"]],LazyAdd];
Notation`AutoLoadNotationPalette = True;



EndPackage[]
