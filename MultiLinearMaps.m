(* ::Package:: *)

(* ::Subsubsection:: *)
(*Prologue*)


BeginPackage["MultiLinearMaps`"];


Unprotect[MapDict,System,AtomicSpace,VecSpace,IndexDict,MultiMap];
ClearAll[MapDict,System,AtomicSpace,VecSpace,IndexDict,MultiMap]
(* Unprotect[Name,Dimension,Type]; 
Unprotect[AtomNames,AtomicQ,AtomDimensions,Atoms,Atomize]; *)
(* Unprotect[Matrixize,Canonicalize];  do these really need to be exposed? *)
Unprotect[SystemMapping,AddMaps,ComposeMaps];
ClearAll[SystemMapping,AddMaps,ComposeMaps]
Unprotect[PartialTrace,MapTranspose,Adjoint,PartialTranspose];
Unprotect[BasisElement,BasisKet,BasisBra,BasisProj];
Unprotect[OmegaKet,OmegaBra,OmegaOp,SwapOp];
Unprotect[ToMatrix,FromMatrix];
Unprotect[AddMaps2,IdentityOp];
ClearAll[AddMaps2];


(*ContractableSystems::usage="ContractableSystem[L,R] returns the system names that are contractable in the composition L \[EmptySmallCircle] R. Input MapDicts."; *)


ComposeMaps::usage="ComposeMaps[L,R] returns the composition L \[EmptySmallCircle] R. Accessible by the infix notation L ** R";
PartialTranspose::usage="PartialTranspose[M,syslist] returns the partial transpose of M with respect to the systems in syslist.";
PartialTrace::usage="PartialTrace[M,syslist] returns the partial trace of M with respect to the systems in syslist. If no systems are explicitly given, all systems that can be traced out are. A single system need not be input as a singleton list.";
MapTranspose::usage="MapTranspose[M] returns the transpose of the map.";
Adjoint::usage="Adjoint[M] returns the adjoint of M.";
SystemMapping::usage="SystemMapping[M] returns a list of two lists, \.7fdescribing which systems M maps to which others: the first sublist records the output systems, the second the input systems.";
AddMaps::usage="AddMaps[M1,M2] returns the sum of the two maps. Accessible infix as M1 + M2.";
ToMatrix::usage="ToMatrix[M,sortinglist] returns the matrix representation of M, with tensor subsystems ordered according to sortinglist.";
FromMatrix::usage="FromMatrix[out,in,m] returns a MultiMap object which maps the systems in the list in to those in out according to the matrix m. If only one list of systems is given, the map takes these systems to themselves.";
BasisBra::usage="BasisBra[sys,k] returns the kth basis bra of system sys.";
BasisKet::usage="BasisKet[sys,k] returns the kth basis ket of system sys.";
BasisProj::usage="BasisProj[sys,k] returns the projector onth the kth basis element of system sys.";
IdentityOp::usage="IdentityOp[syslist] returns the identity operator on the systems in syslist.";
OmegaOp::usage="OmegaOp[sys1,sys2] returns the projector onto the canonical maximally entangled state of systems sys1 and sys2 (no error handling of dimensions yet)";
OmegaKet::usage="OmegaKet[sys1,sys2] returns the ket corresponding to the unnormalized maximally entangled state of systems sys1 and sys2 (no error handling of dimensions yet)";
OmegaBra::usage="OmegaKet[sys1,sys2] returns the bra corresponding to the unnormalized maximally entangled state of systems sys1 and sys2 (no error handling of dimensions yet)";
SwapOp::usage="SwapOp[sys1,sys2] returns the operator which swaps systems sys1 and sys2 (no error handling of dimensions yet)";
AddMaps2::usage="";


(*ValidMappingQ::usage="";
ComposableQ::usage="";
MappingEqualQ::usage="";
ContractableSystemsQ::usage="";
*)


(* Name::usage="Name[x] returns the name of x, a String";
Dimension::usage="Dimension[x] returns the dimension of x, an Integer. If x is a VecSpace object, the dimension of the tensor product space.";
Type::usage="Type[x] gives the type of x, either \"ket\" or \"bra\""; *)


(* AtomNames::usage="";
AtomicQ::usage="";
AtomDimensions::usage="";
Atoms::usage="";
Atomize::usage=""; *)


ComposeMaps::inputs = "Input maps are not composable in this order.";
PartialTranspose::inputs = "Invalid systems for PartialTranspose.";
AddMaps::inputs = "Input maps can not be added together."


Begin["`Private`"];


(* ::Subsubsection:: *)
(*MapDict *)


ContractableSystems[L_MapDict,R_MapDict]:=Intersection[L[[2]],R[[1]]];


rawComposeMaps[L_MapDict,R_MapDict]:=
MapDict@@({Join[L[[1]],Complement[R[[1]],#]],Join[R[[2]],Complement[L[[2]],#]]}&[ContractableSystems[L,R]]);


NonCommutativeMultiply[MapDict[oL_,iL_],MapDict[oR_,iR_]]^:=ComposeMaps[MapDict[oL,iL],MapDict[oR,iR]]


ValidMappingQ[x_MapDict]:=And@@(DuplicateFreeQ/@x);
ComposableQ[L_MapDict,R_MapDict]:=ValidMappingQ[rawComposeMaps[L,R]];
MappingEqualQ[x_MapDict,y_MapDict]:=Equal@@(Sort/@#&/@{x,y});


ComposeMaps[L_MapDict,R_MapDict]:=Module[{cmp=rawComposeMaps[L,R]},If[ValidMappingQ[cmp],cmp,Message[ComposeMaps::inputs]]];


ContractableSystems[x_MapDict]:=
ContractableSystems[x,x]; 
ContractableSystemQ[x_MapDict,sysname_]:=And@@(MemberQ[#,sysname]&/@x);
ContractableSystemsQ[x_MapDict,sysnames_List]:=And@@(SubsetQ[#,sysnames]&/@x);


(* ::Subsubsection:: *)
(*System*)


Name[x_System]:=x[[1]];
Dimension[x_System]:=x[[2]];


(* ::Subsubsection:: *)
(*AtomicSpace*)


Name[x_AtomicSpace]:=Name[x[[1]]]
Dimension[x_AtomicSpace]:=Dimension[x[[1]]];
Type[x_AtomicSpace]:=x[[2]];


(* ::Subsubsection:: *)
(*VecSpace*)


AtomNames[x_VecSpace]:=Level[x,{3}][[;;;;2]];
AtomicQ[x_VecSpace]:=Length[x]==1;
AtomDimensions[x_VecSpace]:=Level[x,{3}][[2;;;;2]];
Dimension[x_VecSpace]:=Times@@AtomDimensions[x];


(* ::Subsubsection:: *)
(*IndexDict*)


Atoms[x_IndexDict]:=Level[x,{2}];
Atomize[x_IndexDict]:=IndexDict@@(VecSpace[#1]&)/@Atoms[x];
AtomicQ[x_IndexDict]:=And@@AtomicQ/@x;
AtomNames[x_IndexDict]:=Level[x,{4}][[1;;All;;2]]


Kets[x_IndexDict]:=Select[Atoms[x],#[[2]]=="ket"&]
Bras[x_IndexDict]:=Select[Atoms[x],#[[2]]=="bra"&]


SystemMapping[x_IndexDict]:=MapDict@@(Map[Name,{Kets[x],Bras[x]},{2}]);
ValidMappingQ[x_IndexDict]:=ValidMappingQ[SystemMapping[x]];
MappingEqualQ[x_IndexDict,y_IndexDict]:=MappingEqualQ[SystemMapping[x],SystemMapping[y]];
ComposableQ[L_IndexDict,R_IndexDict]:=ComposableQ[SystemMapping@L,SystemMapping@R]


ContractableSystemQ[x_IndexDict,sysname_]:=ContractableSystemQ[SystemMapping[x],sysname];
ContractableSystemsQ[x_IndexDict,sysnames_List]:=ContractableSystemsQ[SystemMapping[x],sysnames]


NameSort[x_IndexDict/;AtomicQ[x]]:=IndexDict@@(VecSpace[#]&/@SortBy[Level[x,{2}],{Name,Type[#]=="bra"&}])
TypeSort[x_IndexDict/;AtomicQ[x]]:=IndexDict@@(VecSpace[#]&/@SortBy[Level[x,{2}],{Type[#]=="bra"&,Name}]);
OwnSort[x_IndexDict/;AtomicQ[x],names_List]:=IndexDict@@(VecSpace[#]&/@SortBy[Level[x,{2}],{Type[#]=="bra"&,Position[names,Name[#]][[1,1]]&}])
(* this last one sorts by type and then by name according to a given list of names *)


KetIndices[x_IndexDict]:=Flatten[Position[Atoms[x],z_/;Type[z]=="ket"]];
BraIndices[x_IndexDict]:=Flatten[Position[Atoms[x],z_/;Type[z]=="bra"]]


CompositionIndices[L_IndexDict,R_IndexDict]:=Flatten[{Position[Atoms@L,z_/;Type[z]=="bra"&&Name[z]==#],Position[Atoms@R,z_/;Type[z]=="ket"&&Name[z]==#]}]&/@(ContractableSystems@@(SystemMapping[#]&/@{L,R}));
(* return the index pairs of the tensor that need to be contracted in order to compose the two maps *)


ComposeMaps[L_IndexDict/;AtomicQ[L],R_IndexDict/;AtomicQ[R]]:=With[{ci=CompositionIndices[L,R]},
If[ci=={},IndexDict@@(Join[L,R]),IndexDict@@(Join@@MapThread[Delete,{{L,R},Transpose[{#}]&/@Transpose[ci]}])]]


ContractionIndices[x_IndexDict,sysnames_List]:=If[ContractableSystemsQ[x,sysnames],
With[{atoms=Atoms[x]},
Flatten[{Position[atoms,z_/;Type[z]=="bra"&&Name[z]==#],Position[atoms,z_/;Type[z]=="ket"&&Name[z]==#]}]&/@(sysnames)],{}]


ContractMap[x_IndexDict,sysnames_List]:=If[ContractableSystemsQ[x,sysnames],Module[{r=Select[Atoms[x],!MemberQ[sysnames,Name[#]]&]},If[r=={},IndexDict[],IndexDict[VecSpace@@r]]]]


(* ::Subsubsection:: *)
(*MultiMap*)


AtomicQ[t_MultiMap]:=And[AtomicQ[t[[1]]],List@@Dimension/@Atoms[t[[1]]]==Dimensions[t[[2]]]];Atomize[t_MultiMap]:=
If[AtomicQ[t],t,
Module[{atomdict=Atomize[t[[1]]]},
MultiMap@@{atomdict,ArrayReshape[t[[2]],List@@Dimension/@atomdict]}]];


ComposableQ[L_MultiMap,R_MultiMap]:=ComposableQ[L[[1]],R[[1]]];
SystemMappingEqualQ[t1_MultiMap,t2_MultiMap]:=MappingEqualQ[t1[[1]],t2[[1]]]; 


ComposeAtomicTensors[L_MultiMap,R_MultiMap]:=If[ComposableQ[L[[1]],R[[1]]],MultiMap@@{ComposeMaps[L[[1]],R[[1]]],Activate[TensorContract[Inactive[TensorProduct][L[[2]],R[[2]]],(#+{0,Length[L[[1]]]})&/@CompositionIndices[L[[1]],R[[1]]]]]},Message[ComposeMaps::inputs]]


ComposeMaps[L_MultiMap,R_MultiMap]:=ComposeAtomicTensors[Atomize[L],Atomize[R]];
ComposeMaps[x_MultiMap]:=x;
ComposeMaps[L_MultiMap,R_MultiMap,x__MultiMap]:=ComposeMaps[ComposeMaps[L,R],ComposeMaps[x]]


SystemMapping[t_MultiMap]:=SystemMapping[t[[1]]]


Times[MultiMap[x_,y_],z_?NumericQ]^:=MultiMap[x,z y];
NonCommutativeMultiply[MultiMap[x1_,x2_],MultiMap[y1_,y2_]]^:=ComposeMaps[MultiMap[x1,x2],MultiMap[y1,y2]];


genPerm[list1_,list2_]:=Flatten[Position[list1,#]&/@list2];
SortMap[x_IndexDict/;AtomicQ[x],f_]:=genPerm[List@@(f[x]),List@@x];


Canonicalize[t_MultiMap,sortlist_List:{}]:=
If[Length[t[[1]]]==0,t,
	Module[{sortingf},
		If[sortlist=={},sortingf=TypeSort,sortingf=OwnSort[#,sortlist]&];
		MultiMap@@{sortingf[#[[1]]],Transpose[#[[2]],SortMap[#[[1]],sortingf]]}&[Atomize[t]]
	]
];
AddMaps[t1_MultiMap,t2_MultiMap]:=If[SystemMappingEqualQ[t1,t2],
	Module[{ct1=Canonicalize[t1]},
		MultiMap[ct1[[1]],ct1[[2]]+Canonicalize[t2][[2]]]
	]
];
Plus[MultiMap[x1_,y1_],MultiMap[x2_,y2_]]^:=AddMaps[MultiMap[x1,y1],MultiMap[x2,y2]];
AddMaps2[t1_MultiMap,t2_MultiMap]:=Module[{biglist,one,two},
	biglist=Map[Sort,MapThread[{Complement[#1,#2],Complement[#2,#1]}&,{{Kets[#],Bras[#]}&[t1[[1]]],{Kets[#],Bras[#]}&[t2[[1]]]}],{2}];
	If[Map[Name,biglist[[1]],{2}]==Map[Name,biglist[[2]],{2}],
		one=Canonicalize[t1**IdentityOp[#[[1]]&/@(biglist[[1]][[2]])]];
		two=Canonicalize[t2**IdentityOp[#[[1]]&/@(biglist[[1]][[1]])]];
		MultiMap[one[[1]],one[[2]]+two[[2]]],
		Message[AddMaps::inputs]
	]
]
(* should extract the function which checks for mapping compatibility, as in AddMaps *)


Matrixize[t_MultiMap,sortlist_:{}]:=
Module[{ct,keti,brai},
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


ToMatrix[t_MultiMap,sortlist_:{}]:=Matrixize[t,sortlist][[2]];


(* ::Subsubsection:: *)
(*Constructors*)


BasisElement[sys_System,num_Integer,type_]:=MultiMap@@{IndexDict[VecSpace[AtomicSpace[sys,type]]],SparseArray[{num+1->1},{Dimension[sys]}]};
BasisKet[sys_System,num_Integer]:=BasisElement[sys,num,"ket"];
BasisBra[sys_System,num_Integer]:=BasisElement[sys,num,"bra"];
BasisProj[sys_System,num_Integer]:=BasisKet[sys,num]**BasisBra[sys,num]


SpId[d_]:=SparseArray[{{i_,i_}->1},{d,d}];


IdentityOp[systems_List]:=MultiMap[IndexDict[VecSpace@@(AtomicSpace[#,"ket"]&/@systems),VecSpace@@(AtomicSpace[#,"bra"]&/@systems)],SpId[Times@@(Dimension/@systems)]];


OmegaKet[sys1_System,sys2_System]:=MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"ket"]],VecSpace[AtomicSpace[sys2,"ket"]]],SparseArray@Flatten[IdentityMatrix[Dimension@sys1]]];
OmegaBra[sys1_System,sys2_System]:=MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"bra"]],VecSpace[AtomicSpace[sys2,"bra"]]],SparseArray@Flatten[IdentityMatrix[Dimension@sys1]]];
OmegaOp[sys1_System,sys2_System]:=MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"ket"],AtomicSpace[sys1,"bra"]],VecSpace[AtomicSpace[sys2,"ket"],AtomicSpace[sys2,"bra"]]],SparseArray[IdentityMatrix[(Dimension@sys1)^2]]]


(* Swap[sys1_System,sys2_System]:=PartialTranspose[OmegaOp[sys1,sys2],{Name[sys1]}]; *)
SwapOp[sys1_System,sys2_System]:=MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"bra"],AtomicSpace[sys1,"ket"]],VecSpace[AtomicSpace[sys2,"ket"],AtomicSpace[sys2,"bra"]]],SparseArray[IdentityMatrix[(Dimension@sys1)^2]]]
SwapOp::usage="SwapOp[sys1,sys2] returns the swap operator of the two systems. Input System objects.";


FromMatrix[systems_List,matrix_]:=MultiMap[IndexDict[VecSpace@@(AtomicSpace[#,"ket"]&/@systems),VecSpace@@(AtomicSpace[#,"bra"]&/@systems)],SparseArray@matrix];
FromMatrix[sysout_List,sysin_List,matrix_]:=MultiMap[IndexDict[VecSpace@@(AtomicSpace[#,"ket"]&/@sysout),VecSpace@@(AtomicSpace[#,"bra"]&/@sysin)],SparseArray@matrix]


(* ::Subsubsection:: *)
(*Maps on MultiLinearMaps*)


(* ::Text:: *)
(*Partial Transpose*)


KetAddress[x_IndexDict,sysname_]:=Position[x,z_/;Name[z]==sysname&&Type[z]=="ket",{2}];
BraAddress[x_IndexDict,sysname_]:=Position[x,z_/;Name[z]==sysname&&Type[z]=="bra",{2}]


KetAddresses[x_IndexDict,sysnames_List]:=Position[x,z_/;MemberQ[sysnames,Name[z]]&&Type[z]=="ket",{2}];
BraAddresses[x_IndexDict,sysnames_List]:=Position[x,z_/;MemberQ[sysnames,Name[z]]&&Type[z]=="bra",{2}]


PartialTranspose[x_IndexDict,systems_List]:=
Module[{sysnames=Name/@systems},
	If[ContractableSystemsQ[x,sysnames],
		Module[{k=Join[#,{2}]&/@KetAddresses[x,sysnames],b=Join[#,{2}]&/@BraAddresses[x,sysnames]},
			ReplacePart[x,{k->"bra",b->"ket"}]],
		Message[PartialTranspose::inputs];x
	]
]


PartialTranspose[x_MultiMap,systems_List]:=MultiMap[PartialTranspose[x[[1]],systems],x[[2]]];
PartialTranspose[x_MultiMap,s_System]:=MultiMap[PartialTranspose[x[[1]],{s}],x[[2]]]


(* ::Text:: *)
(*Transpose, Adjoint*)


KetAddresses[x_IndexDict]:=Position[x,z_/;Type[z]=="ket",{2}];
BraAddresses[x_IndexDict]:=Position[x,z_/;Type[z]=="bra",{2}]


MapTranspose[x_MultiMap]:=MultiMap[Module[{k=Join[#,{2}]&/@KetAddresses[x[[1]]],b=Join[#,{2}]&/@BraAddresses[x[[1]]]},
	ReplacePart[x[[1]],{k->"bra",b->"ket"}]],x[[2]]];
Transpose[MultiMap[x_,y_]]^:=MapTranspose[MultiMap[x,y]]


Adjoint[x_MultiMap]:=MultiMap[Module[{k=Join[#,{2}]&/@KetAddresses[x[[1]]],b=Join[#,{2}]&/@BraAddresses[x[[1]]]},
	ReplacePart[x[[1]],{k->"bra",b->"ket"}]],Conjugate[x[[2]]]];


(* ::Text:: *)
(*Partial Trace*)


PartialTrace[x_MultiMap,systems_List:{}]:=
	Module[{sysnames},
		If[systems=={},
			sysnames=ContractableSystems[SystemMapping[x[[1]]]],
			sysnames=Name/@systems
		];
		If[ContractableSystemsQ[x[[1]],sysnames],
			Module[{f=MultiMap[ContractMap[#[[1]],sysnames],TensorContract[#[[2]],ContractionIndices[#[[1]],sysnames]]]&},
				If[AtomicQ[x],
					f[x],
					f[Atomize[x]]
				]
			],
			Message[PartialTrace::inputs];x
		]
	];
PartialTrace[x_MultiMap,s_System]:=PartialTrace[x,{s}];


(* ::Subsubsection:: *)
(*Epilogue*)


End[]

Protect[MapDict,System,AtomicSpace,VecSpace,IndexDict,MultiMap];
Protect[SystemMapping,AddMaps,ComposeMaps];
Protect[PartialTrace,MapTranspose,Adjoint,PartialTranspose];
Protect[BasisElement,BasisKet,BasisBra,BasisProj];
Protect[OmegaKet,OmegaBra,OmegaOp,SwapOp];
Protect[FromMatrix,ToMatrix];
Protect[AddMaps2,IdentityOp];



EndPackage[]
