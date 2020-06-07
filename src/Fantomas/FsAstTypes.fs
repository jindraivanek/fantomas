module Fantomas.FsAstTypes
open FSharp.Compiler.SyntaxTree
open FSharp.Compiler.Range

type Id =
    { Ident: string
      Range: range option }

type FsAstType =
    | Ident
    | SynModuleOrNamespace_AnonModule
    | SynModuleOrNamespace_DeclaredNamespace
    | SynModuleOrNamespace_GlobalNamespace
    | SynModuleOrNamespace_NamedModule
    | SynModuleDecl_ModuleAbbrev
    | SynModuleDecl_NestedModule
    | SynModuleDecl_Let
    | SynModuleDecl_DoExpr
    | SynModuleDecl_Types
    | SynModuleDecl_Exception
    | SynModuleDecl_Open
    | SynModuleDecl_Attributes
    | SynModuleDecl_HashDirective
    | SynModuleDecl_NamespaceFragment
    | SynExpr_Paren
    | SynExpr_Quote
    | SynExpr_Const
    | SynExpr_Typed
    | SynExpr_Tuple
    | SynExpr_StructTuple
    | SynExpr_Record
    | SynExpr_AnonRecd
    | SynExpr_New
    | SynExpr_ObjExpr
    | SynExpr_While
    | SynExpr_For
    | SynExpr_ForEach
    | SynExpr_ArrayOrListOfSeqExpr
    | SynExpr_CompExpr
    | SynExpr_Lambda
    | SynExpr_MatchLambda
    | SynExpr_Match
    | SynExpr_Do
    | SynExpr_Assert
    | SynExpr_App
    | SynExpr_TypeApp
    | SynExpr_LetOrUse
    | SynExpr_TryWith
    | SynExpr_TryFinally
    | SynExpr_Lazy
    | SynExpr_Sequential
    | SynExpr_SequentialOrImplicitYield
    | SynExpr_IfThenElse
    | SynExpr_Ident
    | SynExpr_LongIdent
    | SynExpr_LongIdentSet
    | SynExpr_DotGet
    | SynExpr_DotSet
    | SynExpr_Set
    | SynExpr_DotIndexedGet
    | SynExpr_DotIndexedSet
    | SynExpr_NamedIndexedPropertySet
    | SynExpr_DotNamedIndexedPropertySet
    | SynExpr_TypeTest
    | SynExpr_Upcast
    | SynExpr_Downcast
    | SynExpr_InferredUpcast
    | SynExpr_InferredDowncast
    | SynExpr_Null
    | SynExpr_AddressOf
    | SynExpr_JoinIn
    | SynExpr_ImplicitZero
    | SynExpr_YieldOrReturn
    | SynExpr_YieldOrReturnFrom
    | SynExpr_LetOrUseBang
    | SynExpr_MatchBang
    | SynExpr_DoBang
    | SynExpr_LibraryOnlyILAssembly
    | SynExpr_LibraryOnlyStaticOptimization
    | SynExpr_LibraryOnlyUnionCaseFieldGet
    | SynExpr_LibraryOnlyUnionCaseFieldSet
    | SynExpr_ArbitraryAfterError
    | SynExpr_FromParseError
    | SynExpr_DiscardAfterMissingQualificationAfterDot
    | SynExpr_Fixed
    | RecordField
    | AnonRecordField
    | AnonRecordTypeField
    | SynMemberSig_Member
    | SynMemberSig_Interface
    | SynMemberSig_Inherit
    | SynMemberSig_ValField
    | SynMemberSig_NestedType
    | SynIndexerArg_One
    | SynIndexerArg_Two
    | SynMatchClause_Clause
    | ArgOptions
    | InterfaceImpl
    | TypeDefn
    | TypeDefnSig
    | SynTypeDefnSigRepr_ObjectModel
    | SynTypeDefnSigRepr_Exception
    | SynMemberDefn_Open
    | SynMemberDefn_Member
    | SynMemberDefn_ImplicitCtor
    | SynMemberDefn_ImplicitInherit
    | SynMemberDefn_LetBindings
    | SynMemberDefn_AbstractSlot
    | SynMemberDefn_Interface
    | SynMemberDefn_Inherit
    | SynMemberDefn_ValField
    | SynMemberDefn_NestedType
    | SynMemberDefn_AutoProperty
    | SynSimplePat_Id
    | SynSimplePat_Typed
    | SynSimplePat_Attrib
    | SynSimplePats_SimplePats
    | SynSimplePats_Typed
    | Binding
    | SynValTyparDecls
    | TyparDecl
    | ValSpfn
    | SynPat_Const
    | SynPat_Wild
    | SynPat_Named
    | SynPat_Typed
    | SynPat_Attrib
    | SynPat_Or
    | SynPat_Ands
    | SynPat_LongIdent
    | SynPat_Tuple
    | SynPat_Paren
    | SynPat_ArrayOrList
    | SynPat_Record
    | SynPat_Null
    | SynPat_OptionalVal
    | SynPat_IsInst
    | SynPat_QuoteExpr
    | SynPat_DeprecatedCharRange
    | SynPat_InstanceMember
    | SynPat_FromParseError
    | Pats
    | NamePatPairs
    | ComponentInfo
    | SynTypeDefnRepr_ObjectModel
    | SynTypeDefnRepr_Exception
    | SynTypeDefnKind_TyconUnspecified
    | SynTypeDefnKind_TyconClass
    | SynTypeDefnKind_TyconInterface
    | SynTypeDefnKind_TyconStruct
    | SynTypeDefnKind_TyconRecord
    | SynTypeDefnKind_TyconUnion
    | SynTypeDefnKind_TyconAbbrev
    | SynTypeDefnKind_TyconHiddenRepr
    | SynTypeDefnKind_TyconAugmentation
    | SynTypeDefnKind_TyconILAssemblyCode
    | SynTypeDefnKind_TyconDelegate
    | SynTypeDefnSimpleRepr_None
    | SynTypeDefnSimpleRepr_Union
    | SynTypeDefnSimpleRepr_Enum
    | SynTypeDefnSimpleRepr_Record
    | SynTypeDefnSimpleRepr_General
    | SynTypeDefnSimpleRepr_LibraryOnlyILAssembly
    | SynTypeDefnSimpleRepr_TypeAbbrev
    | SynTypeDefnSimpleRepr_Exception
    | SynExceptionDefn
    | SynExceptionDefnRepr
    | SynAttribute
    | SynAttributeList
    | UnionCase
    | UnionCaseFields
    | UnionCaseFullType
    | EnumCase
    | Field
    | SynType_LongIdent
    | SynType_App
    | SynType_LongIdentApp
    | SynType_Tuple
    | SynType_Array
    | SynType_Fun
    | SynType_Var
    | SynType_Anon
    | SynType_WithGlobalConstraints
    | SynType_HashConstraint
    | SynType_MeasureDivide
    | SynType_MeasurePower
    | SynType_StaticConstant
    | SynType_StaticConstantExpr
    | SynType_StaticConstantNamed
    | SynType_AnonRecd
    | SynValData
    | SynValInfo
    | SynArgInfo
    | ParsedHashDirective
    | SynModuleOrNamespaceSig_AnonModule
    | SynModuleOrNamespaceSig_DeclaredNamespace
    | SynModuleOrNamespaceSig_GlobalNamespace
    | SynModuleOrNamespaceSig_NamedModule
    | SynModuleSigDecl_ModuleAbbrev
    | SynModuleSigDecl_NestedModule
    | SynModuleSigDecl_Types
    | SynModuleSigDecl_Open
    | SynModuleSigDecl_HashDirective
    | SynModuleSigDecl_Exception
    | SynExceptionSig
    | File
    | SigFile
module FsAstType =
    let isSynModuleDecl = function
        | SynModuleDecl_ModuleAbbrev
        | SynModuleDecl_NestedModule
        | SynModuleDecl_Let
        | SynModuleDecl_DoExpr
        | SynModuleDecl_Types
        | SynModuleDecl_Exception
        | SynModuleDecl_Open
        | SynModuleDecl_Attributes
        | SynModuleDecl_HashDirective
        | SynModuleDecl_NamespaceFragment -> true
        | _ -> false
        
    let isSynExpr = function
        | SynExpr_Paren
        | SynExpr_Quote
        | SynExpr_Const
        | SynExpr_Typed
        | SynExpr_Tuple
        | SynExpr_StructTuple
        | SynExpr_Record
        | SynExpr_AnonRecd
        | SynExpr_New
        | SynExpr_ObjExpr
        | SynExpr_While
        | SynExpr_For
        | SynExpr_ForEach
        | SynExpr_ArrayOrListOfSeqExpr
        | SynExpr_CompExpr
        | SynExpr_Lambda
        | SynExpr_MatchLambda
        | SynExpr_Match
        | SynExpr_Do
        | SynExpr_Assert
        | SynExpr_App
        | SynExpr_TypeApp
        | SynExpr_LetOrUse
        | SynExpr_TryWith
        | SynExpr_TryFinally
        | SynExpr_Lazy
        | SynExpr_Sequential
        | SynExpr_SequentialOrImplicitYield
        | SynExpr_IfThenElse
        | SynExpr_Ident
        | SynExpr_LongIdent
        | SynExpr_LongIdentSet
        | SynExpr_DotGet
        | SynExpr_DotSet
        | SynExpr_Set
        | SynExpr_DotIndexedGet
        | SynExpr_DotIndexedSet
        | SynExpr_NamedIndexedPropertySet
        | SynExpr_DotNamedIndexedPropertySet
        | SynExpr_TypeTest
        | SynExpr_Upcast
        | SynExpr_Downcast
        | SynExpr_InferredUpcast
        | SynExpr_InferredDowncast
        | SynExpr_Null
        | SynExpr_AddressOf
        | SynExpr_JoinIn
        | SynExpr_ImplicitZero
        | SynExpr_YieldOrReturn
        | SynExpr_YieldOrReturnFrom
        | SynExpr_LetOrUseBang
        | SynExpr_MatchBang
        | SynExpr_DoBang
        | SynExpr_LibraryOnlyILAssembly
        | SynExpr_LibraryOnlyStaticOptimization
        | SynExpr_LibraryOnlyUnionCaseFieldGet
        | SynExpr_LibraryOnlyUnionCaseFieldSet
        | SynExpr_ArbitraryAfterError
        | SynExpr_FromParseError
        | SynExpr_DiscardAfterMissingQualificationAfterDot
        | SynExpr_Fixed -> true
        | _ -> false
        
    let isSynPat = function
        | SynPat_Const
        | SynPat_Wild
        | SynPat_Named
        | SynPat_Typed
        | SynPat_Attrib
        | SynPat_Or
        | SynPat_Ands
        | SynPat_LongIdent
        | SynPat_Tuple
        | SynPat_Paren
        | SynPat_ArrayOrList
        | SynPat_Record
        | SynPat_Null
        | SynPat_OptionalVal
        | SynPat_IsInst
        | SynPat_QuoteExpr
        | SynPat_DeprecatedCharRange
        | SynPat_InstanceMember
        | SynPat_FromParseError -> true
        | _ -> false

type FsAstProp =
    | Access of SynAccess
    | AppliesToGetterAndSetter of bool
    | AtomicFlag of ExprAtomicFlag
    | C of char
    | C2 of char
    | CommaRanges of range list
    | Const of SynConst
    | Constant of SynConst
    | DebugStr of string
    | DotRange of range
    | FromMethod of bool
    | GetSetRange of range
    | GREATERrange of range
    | Ident of Id
    | Ident2 of Id
    | Ident3 of Id
    | IfToThenRange of range
    | InheritAlias of Id
    | InLambdaSeq of bool
    | InRange of range
    | IsArray of bool
    | IsArrayOrList of bool
    | IsByref of bool
    | IsComGen of bool
    | IsCompilerGenerated of bool
    | IsExnMatch of bool
    | IsFromErrorRecovery of bool
    | IsFromQueryExpression of bool
    | IsFromSource of bool
    | IsInfix of bool
    | IsInline of bool
    | IsList of bool
    | IsModule of SynModuleOrNamespaceKind
    | IsMutable of bool
    | IsNotNakedRefCell of bool
    | IsOptArg of bool
    | IsOptional of bool
    | IsPostfix of bool
    | IsProtected of bool
    | IsRaw of bool
    | IsRecursive of bool
    | IsSelfIdentifier of bool
    | IsStatic of bool
    | IsStruct of bool
    | IsThisVar of bool
    | IsTrueSeq of bool
    | IsUse of bool
    | Kind of SynBindingKind
    | LeftOfSetRange of range
    | LeftParenRange of range
    | LESSrange of range
    | LESSRange of range
    | LongDotId of Id list
    | LongId of Id list
    | LongIdent of Id list
    | MustInline of bool
    | NewExprRange of range
    | Optional of bool
    | PreferPostfix of bool
    | PropKind of MemberKind
    | RangeOfDot of range
    | RefRange of range
    | RightParenRange of range
    | SelfIdent of Id
    | SeqExprOnly of bool
    | SeqPoint of DebugPointAtSequential
    | StaticReq of TyparStaticReq
    | Target of Id
    | TryRange of range
    | TypeArgsRange of range
    | TypeName of Id list
    | WithRange of range
