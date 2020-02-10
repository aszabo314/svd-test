open System
open Aardvark.Base
open Expecto
open FsCheck


type MatrixShape =
    | Full
    | Diagonal
    | Triangular of upper : bool
    | ProperTriangular of upper : bool

type MatrixKind =
    | Arbitrary
    | Constant 
    | Ones     
    | Zeros

type PrettyMatrix<'a> = 
    {
        shape : MatrixShape
        kind : MatrixKind
        rows : int
        cols : int
        value : Matrix<'a>
    }    

let lineRx = System.Text.RegularExpressions.Regex @"(\r\n)|\n"

let indent (str : string) =
    lineRx.Split(str) |> Array.map ((+) "    ") |> String.concat "\n"

let matStr (m : Matrix<float>) =
    let res = 
        Array.init (int m.SX) (fun c -> Array.init (int m.SY) (fun r -> 
            let str = sprintf "%.3f" m.[c,r]
            if str.StartsWith "-" then str
            else " " + str
        ))
    let lens = res |> Array.map (fun col -> col |> Seq.map String.length |> Seq.max)
    let pad (len : int) (s : string) =
        if s.Length < len then s + (System.String(' ',len-s.Length))
        else s

    let padded =
        res |> Array.mapi (fun i col -> 
            col |> Array.map (pad lens.[i])
        )

    String.concat "\n" [
        for r in 0..int m.SY-1 do
            let mutable line = ""
            for c in 0..int m.SX-1 do
                line <- line + " " + padded.[c].[r]
            yield line.Trim()
    ]    


type Arbitraries () = 

    static let properFloat =
        Arb.generate |> Gen.filter (fun v -> not (System.Double.IsNaN(v) || System.Double.IsInfinity(v) || abs(v) > 1E20))

    static let arrayGen (k : MatrixKind) (len : int)=
        match k with
        | Arbitrary -> 
            Gen.arrayOfLength len properFloat
        | Constant -> 
            properFloat |> Gen.map (fun v -> 
                Array.create len v
            )
        | Ones -> 
            Gen.constant (Array.create len 1.0)
        | Zeros -> 
            Gen.constant (Array.zeroCreate len)

    static member GenerateMatrix (r : int, c : int, s : MatrixShape, k : MatrixKind) =
        gen {
            let arrGen = arrayGen k
            match s with
            | Full -> 
                let! fs = arrGen (r*c)
                return Matrix<float>(fs, V2l(c,r))
            | Diagonal -> 
                let! fs = arrGen (min r c)
                return Matrix<float>(V2l(c,r)).SetByCoord(fun (c : V2l) -> if c.X = c.Y then fs.[int c.X] else 0.0 )
            | Triangular(upper) -> 
                let ct =
                    match r <= c, upper with 
                    | true, true -> (r*(r+1))/2+(c-r)*r
                    | true, false -> (r*(r+1))/2
                    | false, true -> (c*(c+1))/2
                    | false, false -> (c*(c+1))/2+(r-c)*c

                let! fs = arrGen ct
                let mutable i = 0
                return Matrix<float>(V2l(c,r)).SetByCoord(fun (c : V2l) ->
                        if upper then
                            if c.Y <= c.X then
                                let v = fs.[i]
                                i <- i+1
                                v
                            else 0.0                        
                        else 
                            if c.Y >= c.X then
                                let v = fs.[i]
                                i <- i+1
                                v    
                            else 0.0                       
                       )
                   
            | ProperTriangular(upper) -> 
                let ct =
                    match r <= c, upper with 
                    | true, true -> (r*  (r-1))/2+(c-r)*r
                    | true, false -> (r* (r-1))/2
                    | false, true -> (c* (c-1))/2
                    | false, false -> (c*(c-1))/2+(r-c)*c

                let! fs = arrGen ct
                let mutable i = 0
                return Matrix<float>(V2l(c,r)).SetByCoord(fun (c : V2l) ->
                        if upper then
                            if c.Y < c.X then
                                let v = fs.[i]
                                i <- i+1
                                v
                            else 0.0                        
                        else 
                            if c.Y > c.X then
                                let v = fs.[i]
                                i <- i+1
                                v    
                            else 0.0                       
                       )
                        
        }

    static member Matrix() =
        gen {
            let! square = Gen.frequency [1, Gen.constant true]      
            let! (r : int) = Gen.choose(1,25)
            let! (c : int) = if square then Gen.constant r else Gen.choose(1,25)
            let! s = Arb.generate<MatrixShape>
            let! k = Arb.generate<MatrixKind>
            let! value = Arbitraries.GenerateMatrix(r, c, s, k)
            return 
                {
                    shape = s
                    kind = k                    
                    rows = r
                    cols = c
                    value = value
                }                
        } |> Arb.fromGen

    static member MatrixFloat() =
        gen {
            let! square = Gen.frequency [1, Gen.constant true; 10, Gen.constant false]      
            let! (r : int) = Gen.choose(1,25)
            let! (c : int) = if square then Gen.constant r else Gen.choose(1,25)
            let! s = Arb.generate<MatrixShape>
            let! k = Arb.generate<MatrixKind>
            let! value = Arbitraries.GenerateMatrix(r, c, s, k)
            return 
                {
                    shape = s
                    kind = k                    
                    rows = r
                    cols = c
                    value = value.Map(float32)
                }                
        } |> Arb.fromGen

let cfg : FsCheckConfig =
    { FsCheckConfig.defaultConfig with 
        maxTest = 10000
        arbitrary = [ typeof<Arbitraries> ] 
    }

let epsilon = 1E-8
let floatEpsilon = 1E-3f

open System.Runtime.CompilerServices

[<Extension; Sealed; AbstractClass>]
type MatrixProperties private() =

    [<Extension>]
    static member IsIdentity(m : Matrix<float>) =
        let mutable maxError = 0.0
        m.ForeachXYIndex (fun (x : int64) (y : int64) (i : int64) ->
            let v = if x = y then 1.0 else 0.0
            let err = abs (m.[i] - v)
            maxError <- max maxError err
        )
        if maxError > epsilon then
            printfn "ERROR: %A" maxError
        maxError <= epsilon

    [<Extension>]
    static member IsIdentity(m : Matrix<float32>) =
        let mutable maxError = 0.0f
        m.ForeachXYIndex (fun (x : int64) (y : int64) (i : int64) ->
            let v = if x = y then 1.0f else 0.0f
            let err = abs (m.[i] - v)
            maxError <- max maxError err
        )
        if maxError > floatEpsilon then
            printfn "ERROR: %A" maxError
        maxError <= floatEpsilon

    [<Extension>]
    static member IsOrtho(m : Matrix<float>) =
        m.Multiply(m.Transposed).IsIdentity()

    [<Extension>]
    static member IsOrtho(m : Matrix<float32>) =
        m.Multiply(m.Transposed).IsIdentity()


    [<Extension>]
    static member IsUpperRight(m : Matrix<float>) =
        let mutable maxError = 0.0
        m.ForeachXYIndex (fun (x : int64) (y : int64) (i : int64) ->
            if x < y then 
                let err = abs m.[i]
                maxError <- max maxError err
        )
        if maxError > epsilon then
            printfn "ERROR: %A" maxError
        maxError <= epsilon

    [<Extension>]
    static member IsUpperRight(m : Matrix<float32>) =
        let mutable maxError = 0.0f
        m.ForeachXYIndex (fun (x : int64) (y : int64) (i : int64) ->
            if x < y then 
                let err = abs m.[i]
                maxError <- max maxError err
        )
        if maxError > floatEpsilon then
            printfn "ERROR: %A" maxError
        maxError <= floatEpsilon
    

    [<Extension>]
    static member ApproximateEquals(a : Matrix<float>, b : Matrix<float>) =
        let err = a.InnerProduct(b,(fun a b -> abs (a-b)),0.0,max)
        if err > epsilon then
            printfn "ERROR: %A" err
        err <= epsilon    

    [<Extension>]
    static member ApproximateEquals(a : Matrix<float32>, b : Matrix<float32>) =
        let err = a.InnerProduct(b,(fun a b -> abs (a-b)),0.0f,max)
        if err > floatEpsilon then
            printfn "ERROR: %A" err
        err <= floatEpsilon    

    [<Extension>]
    static member IsBidiagonal(m : Matrix<float>) =
        let mutable maxError = 0.0
        m.ForeachXYIndex (fun (x : int64) (y : int64) (i : int64) ->
            let err = if (x = y || x = y+1L) then 0.0 else abs m.[i]
            maxError <- max maxError err
        )
        if maxError > epsilon then
            printfn "ERROR: %A" maxError
        maxError <= epsilon 


    [<Extension>]
    static member IsBidiagonal(m : Matrix<float32>) =
        let mutable maxError = 0.0f
        m.ForeachXYIndex (fun (x : int64) (y : int64) (i : int64) ->
            let err = if (x = y || x = y+1L) then 0.0f else abs m.[i]
            maxError <- max maxError err
        )
        if maxError > floatEpsilon then
            printfn "ERROR: %A" maxError
        maxError <= floatEpsilon


    [<Extension>]
    static member IsDiagonal(m : Matrix<float>) =
        let mutable maxError = 0.0
        m.ForeachXYIndex (fun (x : int64) (y : int64) (i : int64) ->
            let err = if x = y then 0.0 else abs m.[i]
            maxError <- max maxError err
        )
        if maxError > epsilon then
            printfn "ERROR: %A" maxError
        maxError <= epsilon 


    [<Extension>]
    static member IsDiagonal(m : Matrix<float32>) =
        let mutable maxError = 0.0f
        m.ForeachXYIndex (fun (x : int64) (y : int64) (i : int64) ->
            let err = if x = y then 0.0f else abs m.[i]
            maxError <- max maxError err
        )
        if maxError > floatEpsilon then
            printfn "ERROR: %A" maxError
        maxError <= floatEpsilon


let qr =
    testList "[QR64] decompose" [
        testPropertyWithConfig cfg "[QR64] Q*R = M" (fun (mat : PrettyMatrix<float>) -> 
            let (q,r) = QR.decompose mat.value
            let res = q.Multiply(r)
            res.ApproximateEquals(mat.value)
        )

        testPropertyWithConfig cfg "[QR64] Q*Qt = ID" (fun (mat : PrettyMatrix<float> ) -> 
            let (q,_) = QR.decompose mat.value
            q.IsOrtho()
        )

        testPropertyWithConfig cfg "[QR64] R = right upper" (fun (mat : PrettyMatrix<float> ) -> 
            let (_,r) = QR.decompose mat.value
            r.IsUpperRight()
        )
    ]    


let qrBidiag = 
    testList "[QR64] bidiagonalize" [
        testPropertyWithConfig cfg "[QR64] U*Ut = ID " (fun (mat : PrettyMatrix<float>) -> 
            let (u,_,_) = QR.Bidiagonalize mat.value
            u.IsOrtho()
        )
        testPropertyWithConfig cfg "[QR64] D is bidiagonal" (fun (mat : PrettyMatrix<float>) -> 
            let (_,d,_) = QR.Bidiagonalize mat.value
            d.IsBidiagonal()
        )

        testPropertyWithConfig cfg "[QR64] V*Vt = ID" (fun (mat : PrettyMatrix<float>) -> 
            let (_,_,vt) = QR.Bidiagonalize mat.value
            vt.IsOrtho()
        )        
        testPropertyWithConfig cfg "[QR64] U*D*Vt = M" (fun (mat : PrettyMatrix<float>) -> 
            let (u,d,vt) = QR.Bidiagonalize mat.value
            let res = u.Multiply(d.Multiply(vt))
            res.ApproximateEquals(mat.value)
        )
    ]    

let svd = 
    testList "[SVD64] decompose" [
        testPropertyWithConfigStdGen (1559202058, 296705199) cfg "[SVD64] U*Ut = ID " (fun (mat : PrettyMatrix<float>) -> 
            match SVD.decompose mat.value with
            | Some (u,_,_) -> u.IsOrtho()
            | None -> true
        )
        // testPropertyWithConfig cfg "[SVD64] S is diagonal" (fun (mat : PrettyMatrix<float>) -> 
        //     match SVD.decompose mat.value with
        //     | Some (_,s,_) -> s.IsDiagonal()
        //     | None -> true
        // )

        // testPropertyWithConfig cfg "[SVD64] V*Vt = ID" (fun (mat : PrettyMatrix<float>) -> 
        //     match SVD.decompose mat.value with
        //     | Some (_,_,vt) -> vt.IsOrtho()
        //     | None -> true
        // )        
        // testPropertyWithConfig cfg "[SVD64] U*S*Vt = M" (fun (mat : PrettyMatrix<float>) -> 
        //     match SVD.decompose mat.value with
        //     | Some (u,s,vt) -> 
        //         let res = u.Multiply(s.Multiply(vt))
        //         res.ApproximateEquals(mat.value)
        //     | None ->
        //         true            
        // )
    ]   


let qr32 =
    testList "[QR32] decompose" [
        testPropertyWithConfig cfg "[QR32] Q*R = M" (fun (mat : PrettyMatrix<float32>) -> 
            let (q,r) = QR.decompose mat.value
            let res = q.Multiply(r)
            res.ApproximateEquals(mat.value)
        )

        testPropertyWithConfig cfg "[QR32] Q*Qt = ID" (fun (mat : PrettyMatrix<float32> ) -> 
            let (q,_) = QR.decompose mat.value
            q.IsOrtho()
        )

        testPropertyWithConfig cfg "[QR32] R = right upper" (fun (mat : PrettyMatrix<float32> ) -> 
            let (_,r) = QR.decompose mat.value
            r.IsUpperRight()
        )
    ]    

let qrBidiag32 = 
    testList "[QR32] Bidiagonalize" [
        testPropertyWithConfig cfg "[QR32] U*Ut = ID " (fun (mat : PrettyMatrix<float32>) -> 
            let (u,_,_) = QR.Bidiagonalize mat.value
            u.IsOrtho()
        )
        testPropertyWithConfig cfg "[QR32] D is bidiagonal" (fun (mat : PrettyMatrix<float32>) -> 
            let (_,d,_) = QR.Bidiagonalize mat.value
            d.IsBidiagonal()
        )

        testPropertyWithConfig cfg "[QR32] V*Vt = ID" (fun (mat : PrettyMatrix<float32>) -> 
            let (_,_,vt) = QR.Bidiagonalize mat.value
            vt.IsOrtho()
        )        
        testPropertyWithConfig cfg "[QR32] U*D*Vt = M" (fun (mat : PrettyMatrix<float32>) -> 
            let (u,d,vt) = QR.Bidiagonalize mat.value
            let res = u.Multiply(d.Multiply(vt))
            res.ApproximateEquals(mat.value)
        )
    ]    
let allTests =
    testList "AllTests" [
        qr
        qrBidiag
        qr32
        qrBidiag32
        svd
    ]
[<EntryPoint>]
let main argv = 
    let mat = Arbitraries.GenerateMatrix(4,4,ProperTriangular true, Ones) |> Gen.eval 0 (FsCheck.Random.StdGen(0,0))



    let (a,b,c) = SVD.decompose mat |> Option.get
    printfn "a:"
    printfn "%s" (matStr a)
    printfn "b:"
    printfn "%s" (matStr b)
    printfn "c:"
    printfn "%s" (matStr c)

    let aorth = a.IsOrtho()
    let corth = c.IsOrtho()

    let m = a.Multiply(b.Multiply(c))
    printfn "M:"
    printfn "%s" (matStr m)
    printfn "real:"
    printfn "%s" (matStr mat)
    Log.line "%A" (m.ApproximateEquals(mat))

    // let cfg = { defaultConfig with parallel = false }
    // Expecto.Tests.runTests cfg svd |> printfn "%A"

    0