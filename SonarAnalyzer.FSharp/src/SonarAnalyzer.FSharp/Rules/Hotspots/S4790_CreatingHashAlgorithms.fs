module SonarAnalyzer.FSharp.Rules.S4790_CreatingHashAlgorithms

open SonarAnalyzer.FSharp
open FSharpAst

// =================================================
// #4790 Hashing data is security-sensitive
// https://rules.sonarsource.com/csharp/type/Security%20Hotspot/RSPEC-4790
// =================================================

module Private =

    [<Literal>]
    let DiagnosticId = "S4790";
    let messageFormat = "Make sure that hashing data is safe here.";
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

    let checkForHashAlgorithmCreation(ctx: TastContext) =
        let checkedDescriptors = 
            [
                "HashAlgorithm.Create"
            ] |> List.map (toNamedTypeDescriptor "System.Security.Cryptography")

        let call =
            ctx.Try<Tast.CallExpr>()
            |> Option.defaultWith (fun _ -> raise EarlyReturn)

        // is a class and method we're interested in?
        if not (checkedDescriptors |> List.contains call.Member) then raise EarlyReturn

        // is it static?
        if call.Expression.IsSome then raise EarlyReturn

        Diagnostic.Create(rule, call.Location, call.Member.DisplayName) |> Some

    let checkForCryptoServiceCreation(ctx: TastContext) =
        let checkedDescriptors = 
            [
                "SHA1CryptoServiceProvider..ctor"
                "MD5CryptoServiceProvider..ctor"
                "HashAlgorithm..ctor"
            ] |> List.map (toNamedTypeDescriptor "System.Security.Cryptography")

        let call =
            ctx.Try<Tast.NewObjectExpr>()
            |> Option.defaultWith (fun _ -> raise EarlyReturn)

        // are we building a class we're interested in?
        if not (checkedDescriptors |> List.contains call.Ctor) then raise EarlyReturn

        Diagnostic.Create(rule, call.Location, call.Ctor.DisplayName) |> Some


    /// check for calls to known encrypt and decrypt calls built into net framework and netstandard
    let checkForCreatingBadObjects (ctx: TastContext) =
        (*
        ISSUES
        ======
        Not enough info on the NewObjectExpr to work out what it inherits from.

        Could add to some global context each time we see an type def for something bad.
        -   Then check that global context each time we see a NewObjectExpr to see if it's a bad'un
        -   Global State. Yuck

        The type def is not an ancestor. It's a sibling.
        -   currently no way to scan for siblings, but shouldn't be hard.
        
        I think something to do with the rec module means that it's resolving
            `use myHash = new MyHashAlgorithm()` as `use myHash = new System.Object()`
        -   Not sure how to resolve this one, I would expect the AST to be correct.
        -   TODO: does this happen if it's not a rec module? suspect not
        
        What happens if it was defined in another file?
        -   We scan files one by one so I would assume that it's not a sibling.

        Is there an order that we scan files? 
        -   What happens if we scan a useage before we scan the file containing the type def
        *)
        None

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
        (checkWithEarlyReturn checkForCreatingBadObjects)
        <|> (checkWithEarlyReturn checkForHashAlgorithmCreation)
        <|> (checkWithEarlyReturn checkForCryptoServiceCreation)
    rule ctx
