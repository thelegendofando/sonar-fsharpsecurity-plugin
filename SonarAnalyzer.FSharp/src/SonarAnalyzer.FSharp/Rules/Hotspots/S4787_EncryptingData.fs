module SonarAnalyzer.FSharp.Rules.S4787_EncryptingData

open SonarAnalyzer.FSharp
open FSharpAst

// =================================================
// #4787 Encrypting data is security-sensitive
// https://rules.sonarsource.com/csharp/type/Security%20Hotspot/RSPEC-4787
// =================================================

module Private =

    [<Literal>]
    let DiagnosticId = "S4787";
    let messageFormat = "Make sure that encrypting data is safe here.";
    let rule = DiagnosticDescriptor.Create(DiagnosticId, messageFormat, RspecStrings.ResourceManager)

    exception EarlyReturn

    let checkWithEarlyReturn f x =
        try
            f x
        with
        | :? EarlyReturn ->
            None

    /// converts Class.Method into a MemberDescriptor in a given namespace
    /// e.g. String.IsNullOrEmpty or Object..ctor
    let toNamedTypeDescriptor nspace (call: string) : Tast.MemberDescriptor =
        let declaring::method::_ = call.Split([|'.'|], 2) |> Array.toList
        let de : Tast.NamedTypeDescriptor = { AccessPath = nspace; DisplayName = declaring; CompiledName = declaring }
        {
            DeclaringEntity = Some de
            CompiledName = method
            DisplayName = method
        }

    /// check for calls to known encrypt and decrypt calls built into net framework and netstandard
    let checkIfCallingEncryptOrDecrypt (ctx: TastContext) =
        let checkedDescriptors = 
            [
                "RSA.Encrypt"
                "RSA.EncryptValue"
                "RSA.Decrypt"
                "RSA.DecryptValue"
                "RSACryptoServiceProvider.Encrypt"
                "RSACryptoServiceProvider.Decrypt"
                "RSACryptoServiceProvider.TryEncrypt"
                "RSACryptoServiceProvider.TryDecrypt"
            ] |> List.map (toNamedTypeDescriptor "System.Security.Cryptography")

        let call =
            ctx.Try<Tast.CallExpr>()
            |> Option.defaultWith (fun _ -> raise EarlyReturn)

        // is a class and method we're interested in?
        if not (checkedDescriptors |> List.contains call.Member) then raise EarlyReturn

        Diagnostic.Create(rule, call.Location, call.Member.DisplayName) |> Some

    /// check if creating encryptors built into net framework and netstandard
    let checkIfCreatingEncrytorsOrDecryptors (ctx: TastContext) =
        let checkedDescriptors = 
            [
                "SymmetricAlgorithm.CreateEncryptor"
                "SymmetricAlgorithm.CreateDecryptor"
            ] |> List.map (toNamedTypeDescriptor "System.Security.Cryptography")

        let call =
            ctx.Try<Tast.CallExpr>()
            |> Option.defaultWith (fun _ -> raise EarlyReturn)

        // is a class and method we're interested in?
        if not (checkedDescriptors |> List.contains call.Member) then raise EarlyReturn

        Diagnostic.Create(rule, call.Location, call.Member.DisplayName) |> Some

    /// check if we're creating new classes that inherit from cryptographic algorithms
    /// e.g. inherit System.Security.Cryptography.AsymmetricAlgorithm()
    let checkForInheritance (ctx: TastContext) =
        let checkedDescriptors = 
            [
                "AsymmetricAlgorithm..ctor"
                "SymmetricAlgorithm..ctor"
                "RSA..ctor"
            ] |> List.map (toNamedTypeDescriptor "System.Security.Cryptography")

        let call =
            // we can't test specifically for `inherits x` so we check for the new object expression
            ctx.Try<Tast.NewObjectExpr>()
            |> Option.defaultWith (fun _ -> raise EarlyReturn)

        // is a class and method we're interested in?
        if not (checkedDescriptors |> List.contains call.Ctor) then raise EarlyReturn

        Diagnostic.Create(rule, call.Location, call.Ctor.DisplayName) |> Some

    let checkForInvocationsOfSubClasses (ctx: TastContext) =
        // TODO: we're just checking for any call to a method that looks like
        // something being encrypted, likely to could false positives. 
        let checkedMembers = 
            [
                "Encrypt"
                "EncryptValue"
                "Decrypt"
                "DecryptValue"
            ]

        let call =
            ctx.Try<Tast.CallExpr>()
            |> Option.defaultWith (fun _ -> raise EarlyReturn)

        // is a class and method we're interested in?
        if not (checkedMembers |> List.contains call.Member.CompiledName) then raise EarlyReturn

        // We don't have any information about what the DeclaringEntity is inheriting from

        Diagnostic.Create(rule, call.Location, call.Member.DisplayName) |> Some

    /// Call the first function and if that fails, call the second function
    let ( <|> ) f g x =
        match (f x) with
        | Some r -> Some r
        | None -> g x

open Private

/// The implementation of the rule
[<Rule(DiagnosticId)>]
let Rule : Rule = fun ctx ->
    let rule =
        (checkWithEarlyReturn checkIfCallingEncryptOrDecrypt)
        <|> (checkWithEarlyReturn checkIfCreatingEncrytorsOrDecryptors)
        <|> (checkWithEarlyReturn checkForInheritance)
        <|> (checkWithEarlyReturn checkForInvocationsOfSubClasses)
    rule ctx
