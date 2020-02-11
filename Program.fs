open System
open Aardvark.Base
open Expecto
open FsCheck

type MatrixTrafo =
    | Id 
    | FlipX
    | FlipY 
    | Transposed
    | RandomMask

type MatrixShape =
    | Full
    | Diagonal
    | Triangular of upper : bool
    | ProperTriangular of upper : bool
    | CopyRows
    | CopyCols

type MatrixKind<'a> =
    | Arbitrary
    | Constant of 'a
    | Ones     
    | Zeros

type PrettyMatrix<'a> = 
    {
        shape : MatrixShape
        kind : MatrixKind<'a>
        trafo : MatrixTrafo
        rows : int
        cols : int
        value : Matrix<'a>
    }    

let lineRx = System.Text.RegularExpressions.Regex @"(\r\n)|\n"

let indent (str : string) =
    lineRx.Split(str) |> Array.map ((+) "    ") |> String.concat "\n"

let inline matStr (m : Matrix< ^a >) =
    let res = 
        Array.init (int m.SX) (fun c -> Array.init (int m.SY) (fun r -> 
            let str = sprintf "%.3f" (float m.[c,r])
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

let inline printMat (name : string) (m : NativeMatrix< ^a >) =
    let res = 
        Array.init (int m.SX) (fun c -> Array.init (int m.SY) (fun r -> 
            let str = sprintf "%.3f" (float m.[c,r])
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
            
    System.Console.WriteLine("{0}", name)
    for r in 0..int m.SY-1 do
        let mutable line = ""
        for c in 0..int m.SX-1 do
            line <- line + " " + padded.[c].[r]
        System.Console.WriteLine("    {0}", line.Trim())



type Arbitraries () = 

    static let properFloat =
        Arb.generate |> Gen.filter (fun v -> not (System.Double.IsNaN(v) || System.Double.IsInfinity(v) || abs(v) > 1E20 || abs(v) < 1E-20))

    static let arrayGen (k : MatrixKind<float>) (len : int)=
        match k with
        | Arbitrary -> 
            Gen.arrayOfLength len properFloat
        | Constant v -> 
            Gen.constant (Array.create len v)
        | Ones -> 
            Gen.constant (Array.create len 1.0)
        | Zeros -> 
            Gen.constant (Array.zeroCreate len)

    static member GenerateMatrix (r : int, c : int, s : MatrixShape, k : MatrixKind<float>, t : MatrixTrafo) =
        gen {
            let arrGen = arrayGen k
            let! mat = 
                gen {
                    match s with
                    | Full -> 
                        let! fs = arrGen (r*c)
                        return Matrix<float>(fs, V2l(c,r))
                    | Diagonal -> 
                        let! fs = arrGen (min r c)
                        return Matrix<float>(V2l(c,r)).SetByCoord(fun (c : V2l) -> if c.X = c.Y then fs.[int c.X] else 0.0 )
                    | CopyCols -> 
                        let! fs = arrGen r
                        return Matrix<float>(V2l(c,r)).SetByCoord(fun (c : V2l) -> fs.[int c.Y])    
                    | CopyRows -> 
                        let! fs = arrGen c
                        return Matrix<float>(V2l(c,r)).SetByCoord(fun (c : V2l) -> fs.[int c.X])                             
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
            let! trafoed = 
                gen {
                    match t with
                    | Id -> return mat
                    | FlipX -> 
                        let mo : Matrix<float> = mat.Copy()
                        return mat.SetByCoord(fun (c : V2l) -> mo.[mo.SX-1L-c.X, c.Y])
                    | FlipY -> 
                        let mo : Matrix<float> = mat.Copy()
                        return mat.SetByCoord(fun (c : V2l) -> mo.[c.X, mo.SY-1L-c.Y])
                    | Transposed ->
                        return mat.Transposed
                    | RandomMask ->
                        let! mask = Gen.arrayOfLength (r*c) Arb.generate<bool>
                        return mat.SetByIndex(fun i -> if mask.[int i] then mat.[i] else 0.0)
                }
                
            return trafoed            
        }
        
    static member MatrixKind() = 
        gen {
            let! ctor = Gen.frequency [1, Gen.constant Arbitrary; 1, Gen.constant Ones; 1, Gen.constant Zeros; 1, Gen.constant (Constant 0.0)]      
            match ctor with
            | Constant _ ->
                let! f = properFloat
                return Constant f
            | e ->
                return e
        } |> Arb.fromGen
        
    static member Matrix() =
        gen {
            let! square = Gen.frequency [1, Gen.constant true; 10, Gen.constant false]      
            let! (r : int) = Gen.choose(1,25)
            let! (c : int) = if square then Gen.constant r else Gen.choose(1,25)
            let! s = Arb.generate<MatrixShape>
            let! k = Arb.generate<MatrixKind<float>>
            let! t = Arb.generate<MatrixTrafo>


            let! value = Arbitraries.GenerateMatrix(r, c, s, k,t)
            return 
                {
                    shape = s
                    kind = k                    
                    trafo = t
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
            let! k = Arb.generate<MatrixKind<float>>
            let! t = Arb.generate<MatrixTrafo>


            let! value = Arbitraries.GenerateMatrix(r, c, s, k,t)
            let k =
                match k with
                | Zeros -> Zeros
                | Ones -> Ones
                | Constant v -> Constant (float32 v)
                | Arbitrary -> Arbitrary

            return 
                {
                    shape = s
                    kind = k                    
                    trafo = t
                    rows = r
                    cols = c
                    value = value.Map(float32)
                }                
        } |> Arb.fromGen

let cfg : FsCheckConfig =
    { FsCheckConfig.defaultConfig with 
        maxTest = 100000
        arbitrary = [ typeof<Arbitraries> ] 
    }

let epsilon = 1E-8
let floatEpsilon = 0.1f

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
    static member MaxDiff(a : Matrix<float>, b : Matrix<float>) =
        a.InnerProduct(b,(fun a b -> abs (a-b)),0.0,max)
        
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


    [<Extension>]
    static member DecreasingDiagonal(m : Matrix<float>) =
        let mutable wrong = []
        let mutable last = System.Double.PositiveInfinity
        m.ForeachXYIndex (fun (x : int64) (y : int64) (i : int64) ->
            if x = y then 
                if m.[i] > last then
                    wrong <- (last, m.[i]) :: wrong
                last <- m.[i]
        )
        match wrong with
        | [] -> 
            true
        | wrong ->  
            printfn "ERROR: %A" wrong
            false

            

    [<Extension>]
    static member DecreasingDiagonal(m : Matrix<float32>) =
        let mutable wrong = []
        let mutable last = System.Single.PositiveInfinity
        m.ForeachXYIndex (fun (x : int64) (y : int64) (i : int64) ->
            if x = y then 
                if m.[i] > last then
                    wrong <- (last, m.[i]) :: wrong
                last <- m.[i]
        )
        match wrong with
        | [] -> 
            true
        | wrong ->  
            printfn "ERROR: %A" wrong
            false

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
        testPropertyWithConfig cfg "[SVD64] U*Ut = ID " (fun (mat : PrettyMatrix<float>) -> 
            match SVD.decompose mat.value with
            | Some (u,_,_) -> u.IsOrtho()
            | None -> true
        )
        testPropertyWithConfig cfg "[SVD64] S is diagonal" (fun (mat : PrettyMatrix<float>) -> 
            match SVD.decompose mat.value with
            | Some (_,s,_) -> s.IsDiagonal()
            | None -> true
        )
        
        testPropertyWithConfig cfg "[SVD64] S is decreasing" (fun (mat : PrettyMatrix<float>) -> 
            match SVD.decompose mat.value with
            | Some (_,s,_) -> s.DecreasingDiagonal()
            | None -> true
        )

        testPropertyWithConfig cfg "[SVD64] V*Vt = ID" (fun (mat : PrettyMatrix<float>) -> 
            match SVD.decompose mat.value with
            | Some (_,_,vt) -> vt.IsOrtho()
            | None -> true
        )        
        testPropertyWithConfig cfg "[SVD64] U*S*Vt = M" (fun (mat : PrettyMatrix<float>) -> 
            match SVD.decompose mat.value with
            | Some (u,s,vt) -> 
                let res = u.Multiply(s.Multiply(vt))
                res.ApproximateEquals(mat.value)
            | None ->
                true            
        )
    ]   
  

let svd32 = 
    testList "[SVD32] decompose" [
        testPropertyWithConfig cfg "[SVD32] U*Ut = ID " (fun (mat : PrettyMatrix<float32>) -> 
            match SVD.decompose mat.value with
            | Some (u,_,_) -> u.IsOrtho()
            | None -> true
        )
        testPropertyWithConfig cfg "[SVD32] S is diagonal" (fun (mat : PrettyMatrix<float32>) -> 
            match SVD.decompose mat.value with
            | Some (_,s,_) -> s.IsDiagonal()
            | None -> true
        )
        
        testPropertyWithConfig cfg "[SVD32] S is decreasing" (fun (mat : PrettyMatrix<float32>) -> 
            match SVD.decompose mat.value with
            | Some (_,s,_) -> s.DecreasingDiagonal()
            | None -> true
        )

        testPropertyWithConfig cfg "[SVD32] V*Vt = ID" (fun (mat : PrettyMatrix<float32>) -> 
            match SVD.decompose mat.value with
            | Some (_,_,vt) -> vt.IsOrtho()
            | None -> true
        )        
        testPropertyWithConfig cfg "[SVD32] U*S*Vt = M" (fun (mat : PrettyMatrix<float32>) -> 
            match SVD.decompose mat.value with
            | Some (u,s,vt) -> 
                let res = u.Multiply(s.Multiply(vt))
                res.ApproximateEquals(mat.value)
            | None ->
                true            
        )
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
        //qr32
        //qrBidiag32
        svd
        //svd32
    ]
[<EntryPoint>]
let main argv =
    // Aardvark.Init()

    // let img = PixImage.Create(@"C:\Users\Schorsch\Desktop\images\IMG_6975.jpg").ToPixImage<byte>()

   
    // let trans (m : Matrix<float>) =
    //     let mutable (u, s, vt) = SVD.decompose m |> Option.get

    //     let diag = int (min s.SX s.SY)
    //     for i in 0 ..diag - 1 do
    //         s.[i,i] <- ((abs s.[i,i] / s.[0,0]) ** (1.0 / 1.2)) *  s.[0,0]
    //     u.Multiply(s.Multiply(vt))

    // let toImg (m : Matrix<float>) (l : float) (h : float) =
    //     let img = PixImage<byte>(Col.Format.RGBA, V2i m.Size)
    //     img.GetMatrix<C4b>().SetMap(m, fun v -> 
    //         let b = 255.0 * ((v - l) / (h - l) |> clamp 0.0 1.0) |> byte
    //         C4b(b,b,b,255uy)
    //     ) |> ignore
    //     img

        
    // let toImgRGB (r : Matrix<float>) (g : Matrix<float>) (b: Matrix<float>) (l : float) (h : float) =
    //     let img = PixImage<byte>(Col.Format.RGBA, V2i r.Size)
    //     img.GetMatrix<C4b>().SetMap3(r, g, b, fun r g b -> 
    //         let r = 255.0 * ((r - l) / (h - l) |> clamp 0.0 1.0) |> byte
    //         let g = 255.0 * ((g - l) / (h - l) |> clamp 0.0 1.0) |> byte
    //         let b = 255.0 * ((b - l) / (h - l) |> clamp 0.0 1.0) |> byte
    //         C4b(r,g,b,255uy)
    //     ) |> ignore
    //     img

    // let fr = Matrix<float>(img.Size)
    // let fg = Matrix<float>(img.Size)
    // let fb = Matrix<float>(img.Size)
    // fr.SetMap(img.GetMatrix<C4b>(), fun c -> float c.R / 255.0) |> ignore
    // fg.SetMap(img.GetMatrix<C4b>(), fun c -> float c.G / 255.0) |> ignore
    // fb.SetMap(img.GetMatrix<C4b>(), fun c -> float c.B / 255.0) |> ignore
        

    // let r = trans fr
    // let g = trans fg
    // let b = trans fb

    // (toImgRGB r g b 0.0 1.0).SaveAsImage @"C:\Users\Schorsch\Desktop\comp.png"

    //(toImg u -1.0 1.0).SaveAsImage @"C:\Users\Schorsch\Desktop\U.png"
    //(toImg vt -1.0 1.0).SaveAsImage @"C:\Users\Schorsch\Desktop\Vt.png"
    //(toImg s 0.0 s.[0,0]).SaveAsImage @"C:\Users\Schorsch\Desktop\S.png"




    // let mat = Arbitraries.GenerateMatrix(11,17,CopyCols,Arbitrary,FlipY) |> Gen.eval 0 (FsCheck.Random.StdGen(797839475, 296705616))

    // let (u,s,vt) = SVD.decompose mat |> Option.get
    // printfn "u:"
    // printfn "%s" (matStr u)
    // printfn "s:"
    // printfn "%s" (matStr s)
    // printfn "vt:"
    // printfn "%s" (matStr vt)

    // let d = s.IsDiagonal()
    // let aorth = u.IsOrtho()
    // let corth = vt.IsOrtho()

    // let m = u.Multiply(s.Multiply(vt))
    // printfn "M:"
    // printfn "%s" (matStr m)
    // printfn "real:"
    // printfn "%s" (matStr mat)
    // Log.line "%A" (m.ApproximateEquals(mat))

    let cfg = { defaultConfig with parallel = true }
    Expecto.Tests.runTests cfg allTests |> printfn "%A"

    0