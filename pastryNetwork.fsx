#r "bin/Debug/netcoreapp3.1/Akka.dll"
#r "bin/Debug/netcoreapp3.1/Akka.FSharp.dll"
#time "on"

open System
open Akka
open Akka.Actor
open System.Collections.Generic
open Akka.FSharp
open System.Security.Cryptography

let system = System.create "system" (Configuration.defaultConfig())

// Defining variables here
let globalList = new List<String>() 
//let mutable globalSet = Set.empty
let mutable globalRef = Map.empty<String,IActorRef>
let random = System.Random()
let mutable myCreator = null
let mutable myPastryModerator = null
let sha = SHA256.Create()
let mutable numToHashMap = Map.empty
let mutable starterActor = null

let ByteToHex bytes = 
    bytes 
    |> Array.map (fun (x : byte) -> System.String.Format("{0:X2}", x))
    |> String.concat System.String.Empty

let args = fsi.CommandLineArgs

let n = (int) args.[1]
let nofreq = (int) (args.[2])

for i = 0 to n do
    let b = sha.ComputeHash(System.Text.Encoding.ASCII.GetBytes (i.ToString()))
    let res =  ByteToHex b
    numToHashMap <- numToHashMap.Add(i,res.[0..8])

type allset = struct
    val id: String
    val sector: int
    val actorRef: IActorRef
    val ns: Set<String>
    val maxls: Set<String>
    val minls: Set<String>
    val RT: List<List<String>>
    val map: Map<String,IActorRef>

    new (nodeId,sect, ref, neighborset, maxleaf, minleaf, routingtable,refmap) =
        {id = nodeId; sector = sect; actorRef = ref; ns = neighborset; maxls = maxleaf; minls = minleaf; RT = routingtable;  map = refmap }

end
    

type creatorCommand = 
    | CreateNode of int

type moderatorCommand = 
    | AddNode of String*int
    | StartNow of String
    | HopCount of int

type pastryCommand = 
    | Instantiate of String*int
    | AddToNetwork of int*String*int*IActorRef*Map<int,allset>
    | Route of String*String*int
    | Delivery of String*int
    | AddedToNetwork of Map<int,allset>
    | Update of String*IActorRef
    | StartRouting of Map<String,IActorRef>*int*Map<int,String>
    

type starterCommand = 
    | Start of int
    | Done of String


    // Pastry Node
let pastryNode (mailbox : Actor<_>) =
    let RT = new List<List<String>>()
    for i = 0 to 8 do 
        let list = new List<String>()
        for j = 0 to 15 do
            list.Add("g")
        RT.Add(list)

    //function for getting value fron string id
    let convertToUint (nodeId : String) = 
        let num = Convert.ToUInt64(nodeId,16) 
        num

    //prefix match 
    let matchTwoStrings (x:string) (y:string) =
        let mutable l=0
        while l<=8 && x.[l]=y.[l] do
            l<-l+1
        l
    
    let mutable min_LeafValue = Math.Pow(16.0,11.0) |>uint64
    let mutable max_LeafValue = -1 |>uint64
    let mutable min = Math.Pow(16.0,11.0) |>uint64

    let mutable neighborhood = Set.empty<String>
    let mutable maxLeafSet = Set.empty<String>
    let mutable minLeafSet = Set.empty<String>

    //String id to actor reference
    let mutable refMap = Map.empty<String,IActorRef>
    let mutable valueMap = Map.empty<String,uint64>

    //Specefic identifiers of a pastry node
    let mutable nodeId = ""
    let mutable myvalue = 0 |>uint64
    let mutable sector = 0


    let routingAlgorithm (keyString: String) =
        let mutable nextActor = null
        let key = convertToUint keyString
        let l = matchTwoStrings keyString nodeId
        if keyString <> nodeId then
            
            if (key >= min_LeafValue && key <= max_LeafValue) then 
                for i in (Set.union maxLeafSet minLeafSet) do 
                    let value = Math.Max(myvalue,convertToUint i) - Math.Min(myvalue,convertToUint i)
                    if ( value < min) then 
                        nextActor <- refMap.[i] 
                        min <- value
            else 
                for i = 0 to 15 do
                    let currentString = RT.[l].[i]
                    if currentString <> "g" then 
                        let templ = matchTwoStrings currentString keyString
                        if(templ > l) then 
                            nextActor <- refMap.[currentString]
                if (nextActor = null) then 
                    let mutable fullList = Set.empty
                    for i in neighborhood do 
                        fullList <- fullList.Add(i)
                    for i in (Set.union maxLeafSet minLeafSet) do 
                        fullList <- fullList.Add(i)
                    for j = 0 to 8 do
                        for i = 0 to RT.[j].Count-1 do 
                            if RT.[j].[i] <> "g" then
                                fullList <- fullList.Add(RT.[j].[i])
                    
                    for i in fullList do 
                        let currentActor = i
                        let currentActorValue = convertToUint currentActor
                        let templ = matchTwoStrings currentActor keyString
                        let keyDiff = Math.Max(myvalue,key) - Math.Min(myvalue,key)
                        let currentDiff = Math.Max(currentActorValue,key) - Math.Min(currentActorValue,key)
                        if ( keyDiff > currentDiff && templ>=l) then 
                            nextActor <- refMap.[currentActor]
        nextActor
    
    let diffrence secondActor= 
        let diff = Math.Max(myvalue,secondActor) - Math.Min(myvalue,secondActor)
        diff

    let findMax set = 
        let mutable max = -1 |>uint64
        let mutable current = null
        for i in set do
            let diff = diffrence valueMap.[i]
            if (diff > max) then 
                max <- diff
                current <- i
        current

    let updatemin = 
        let mutable minimum = min_LeafValue
        for i in minLeafSet do 
            let value = convertToUint i
            if (value < minimum) then 
                minimum <- value
        min_LeafValue <- minimum

    let updatemax = 
        let mutable maximum = max_LeafValue
        for i  in maxLeafSet do 
            let value = convertToUint i
            if value > maximum then 
                maximum <- value
        max_LeafValue <- maximum
                

    let updateleaf actor ref = 
        if actor <> nodeId then
            let value = valueMap.[actor]
            let diff = diffrence value
            if (myvalue < value) then 
                if maxLeafSet.Count < 8 then 
                    maxLeafSet <- maxLeafSet.Add(actor)
                else
                    let maxActor = findMax maxLeafSet
                    if maxActor <> null then
                        let currdiff = diffrence valueMap.[maxActor]
                        if (currdiff > diff) then 
                            maxLeafSet <- maxLeafSet.Remove(maxActor)
                            maxLeafSet <- maxLeafSet.Add(actor)
            else
                if minLeafSet.Count < 8 then 
                    minLeafSet <- minLeafSet.Add(actor)
                else
                    let maxActor = findMax minLeafSet
                    if maxActor <> null then
                        let currdiff = diffrence valueMap.[maxActor]
                        if (currdiff > diff) then 
                            minLeafSet <- minLeafSet.Remove(maxActor)
                            minLeafSet <- minLeafSet.Add(actor)

    let updatens actor ref=
        let value = valueMap.[actor]
        let diff = diffrence value
        if neighborhood.Count<32 then 
            neighborhood <- neighborhood.Add(actor)

    let rand = System.Random()

    let rec loop() = actor {
        let! msg = mailbox.Receive()
        match msg with
        | Instantiate (id,sect) ->
            nodeId <- id
            sector <- sect
            myvalue <-  convertToUint nodeId
        | Route (msg,keyString,hop) -> 
            let nextActor = routingAlgorithm keyString
            if nextActor = null then 
                mailbox.Self <! Delivery (msg,hop)
            else
                nextActor <! Route (msg,keyString,hop+1)
        | Delivery (msg,hop) -> 
            myPastryModerator <! HopCount hop
        | AddToNetwork (hop,id,sect,actorRef,map) ->
            let mutable myMap = map
            myMap <-myMap.Add(hop,new allset(nodeId,sect,mailbox.Self,neighborhood,maxLeafSet,minLeafSet,RT,refMap))
            let mutable nextActor = routingAlgorithm id
                
            if nextActor = null then 
                actorRef <! AddedToNetwork myMap
                
            else
                nextActor <! AddToNetwork (hop+1,id,sect,actorRef,myMap)
        
        | AddedToNetwork (myMap) ->
            let map = myMap
            let mutable current = 0
            for i = 0 to map.Count-1 do
                refMap <- refMap.Add(map.[i].id,map.[i].actorRef)
                valueMap <- valueMap.Add(map.[i].id, convertToUint map.[i].id)
                let l = matchTwoStrings nodeId map.[i].id
                if i = 0 then
                    for j in map.[i].ns do 
                        if j <> nodeId then 
                            neighborhood <- neighborhood.Add(j)
                            refMap <- refMap.Add(j,map.[i].map.[j])

                if i = map.Count-1 then
                    for j in map.[i].maxls do 
                        if convertToUint j > myvalue then 
                            maxLeafSet <- maxLeafSet.Add(j)
                            refMap <- refMap.Add(j,map.[i].map.[j])
                    for j in map.[i].minls do 
                        if convertToUint j < myvalue then 
                            minLeafSet <- minLeafSet.Add(j)
                            refMap <- refMap.Add(j,map.[i].map.[j])

                if map.Count < 8 then  
                    for j = current to l do 
                        for k = 0 to 15 do 
                            if (map.[i].RT.[j].[k] <> "g") then 
                                RT.[j].[k] <- map.[i].RT.[j].[k]
                                refMap <- refMap.Add(map.[i].RT.[j].[k],map.[i].map.[RT.[j].[k]])
                
                    current <- l + 1

                for i in refMap do
                    valueMap <- valueMap.Add(i.Key, convertToUint i.Key)


                if map.[i].id <> nodeId then
                    updateleaf map.[i].id map.[i].actorRef
                    updatens map.[i].id map.[i].actorRef
                updatemin
                updatemax

            for i in refMap do 
                refMap.[i.Key] <! Update (nodeId,mailbox.Self)

            starterActor <! Done "done!"

        | Update (actor,ref) ->
            refMap <- refMap.Add(actor,ref)
            valueMap <- valueMap.Add(actor,convertToUint actor)
            updateleaf actor ref
            updatens actor ref
            updatemin
            updatemax

            let l = matchTwoStrings nodeId actor
            if (l<9) then 
                let x = actor.[l] |>string
                let n = convertToUint x |>int
                if RT.[l].[n] = "g" then 
                    RT.[l].[n] <- actor
                    
        | StartRouting (map,num,numMap) ->
            for i = 1 to num do 
                let x = rand.Next(0,numMap.Count) 
                system.Scheduler.ScheduleTellOnce(TimeSpan.FromSeconds(i |> float),mailbox.Self, Route ("msg",numMap.[x],0))

         
        return! loop()
    }
    loop()

let creator  (mailbox : Actor<_>) =
    let rec loop() = actor {
        let! msg = mailbox.Receive()
        match msg with
        | CreateNode num ->
            let id = numToHashMap.[num]
            let sector = 2
            let actor = spawn system id pastryNode
            globalRef <- globalRef.Add(id, actor)
            globalRef.[id] <! Instantiate (id,sector)
            
            myPastryModerator <! AddNode (id,sector)
        return! loop()
    }
    loop()


let mutable reqArrived = 0
let mutable allHop = 0
let pastryModerator  (mailbox : Actor<_>) =
    let mutable sectorMap = Map.empty<int,List<String>>
    for i= 1 to 12 do 
        let list = new List<String>()  
        sectorMap <- sectorMap.Add(i,list)
    let rec loop() = actor {
        let! msg = mailbox.Receive()
        match msg with
        | AddNode (node_id,sector) ->
            if globalList.Count > 0 then 
                if (sectorMap.[sector].Count = 0) then
                    let random_num = random.Next(0,globalList.Count)
                    globalRef.[node_id] <! AddToNetwork (0,node_id,sector,globalRef.[node_id],Map.empty)
                else
                    let random_num = random.Next(0,sectorMap.[sector].Count)
                    globalRef.[sectorMap.[sector].[random_num]] <! AddToNetwork (0,node_id,sector,globalRef.[node_id],Map.empty)
            else 
                starterActor <! Done "done!"
            sectorMap.[sector].Add(node_id)
            globalList.Add(node_id)

        | StartNow msg ->
            for i in globalRef do 
                globalRef.[i.Key] <! StartRouting (globalRef,nofreq,numToHashMap)

        | HopCount (hop) ->
            reqArrived <- reqArrived + 1
            allHop <- allHop + hop
            
        return! loop()
    }
    loop()

myCreator <- spawn system "creator" creator
myPastryModerator <- spawn system "pastryModerator" pastryModerator

let mutable nofActor = 0  
let starter  (mailbox : Actor<_>) =
   
    let rec loop() = actor {
        let! msg = mailbox.Receive()
        match msg with
        | Start num ->
            if (nofActor < n) then
                myCreator <! CreateNode num
        | Done msg->
            nofActor <- nofActor + 1
            mailbox.Self <! Start nofActor
        return! loop()
    }
    loop()

starterActor <- spawn system "starter" starter
starterActor <! Start 0 
let mutable count = 0

while (nofActor<n) do 
    count <- count+1

//printfn "Network build Successfull"
myPastryModerator <! StartNow "start"
    
while (reqArrived < n*nofreq) do
    count <- count + 1 

let AH = allHop |> float
let Allreq = n*nofreq |> float
printfn "Average number of hops: %f"  (AH/Allreq)