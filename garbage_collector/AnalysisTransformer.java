import java.util.*;
import soot.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.toolkits.scalar.LiveLocals;
import soot.jimple.*;
import java.util.regex.Pattern;
import java.util.regex.Matcher;
import soot.util.Chain;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;


public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;
    private static TreeMap<String,  TreeMap<String,String>> Answer = new TreeMap<>();
    private static TreeMap<String,String> Dead=new TreeMap<>();
    private static class Pair<K, V, M, R> {
        private K key;
        private V value;
        private M map_ctx;
        private R return_ctx;

        private Pair(K key, V value, M map_ctx, R return_ctx) {
            this.key = key;
            this.value = value;
            this.map_ctx=map_ctx;
            this.return_ctx=return_ctx;
        }

        public K getKey() { return key; }
        public V getValue() { return value; }
        public M getmap_ctx(){return map_ctx;}
        public R getreturn_ctx(){return return_ctx;}

        public static <K, V, M, R > Pair<K, V, M, R > of(K key, V value, M map_ctx, R return_ctx) {
            return new Pair<>(key, value, map_ctx, return_ctx);
        }
    }
    
    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {
        Set<SootMethod> methods = new LinkedHashSet <>();
        Pair<Map<String, Set<String>>, Map<AbstractMap.SimpleEntry<String, String>, Set<String>>, LinkedHashMap<String,String>,Set<String>> p;
        cg = Scene.v().getCallGraph();
        List<Edge> edgesToRemove = new ArrayList<>();
        for (Iterator<Edge> edgeIter = cg.iterator(); edgeIter.hasNext();) {
            Edge edge = edgeIter.next();
            SootMethod tgt = edge.tgt();
            if (tgt.getName().equals("<init>")) {
                // Add edge to the removal list
                edgesToRemove.add(edge);
            }
        }

        for (Edge edge : edgesToRemove) {
            cg.removeEdge(edge);
        }
        // Get the main method
        SootMethod mainMethod = Scene.v().getMainMethod();
        // Get the list of methods reachable from the main method
        // Note: This can be done bottom up manner as well. Might be easier to model.
        p=getlistofMethods(mainMethod, methods, new LinkedHashMap<>());
        printAnswer();
        // for 
        // (SootMethod m : methods) {
        //     System.out.println(m);
        //     processCFG(m);
        // }
    }

    protected static void recur(String l, Map<String, Set<String>> stackGraph,Map<AbstractMap.SimpleEntry<String, String>, Set<String>> heapGraph, int lineNum){
        if(l=="null"){return;}
        for(Map.Entry<AbstractMap.SimpleEntry<String,String>,Set<String>> e : heapGraph.entrySet()){
            if(l.equals(e.getKey().getKey())){
                for(String s: e.getValue()){
                    //int f=0;
                    // for(Map.Entry<String,Set<String>> e1 : stackGraph.entrySet()){
                    //     if(e1.getValue().contains(s)){
                    //         f=1;
                    //     }
                    // }
                   // if(f==0){
                    if(s!= "null"){
                        // System.out.println("fffffffff");
                        Dead.put(s,String.valueOf(lineNum));
                        // System.out.println(Dead);
                        // System.out.println("Dead at " + lineNum);
                        recur(s,stackGraph,heapGraph,lineNum);
                    }
                    //}
                }
            }
        }
    }
    
    protected static void processCFG(SootMethod method,Map<String, Set<String>> stackGraph,Map<AbstractMap.SimpleEntry<String, String>, Set<String>> heapGraph) {
        if(method.toString().contains("init")  ) { return; }
        
        //if(stackGraph.isEmpty() && heapGraph.isEmpty()){return;}

        // System.out.println(method.toString());
        Body body = method.getActiveBody();
        Chain<Local> local = body.getLocals();
        List<Local> locals= new ArrayList<>(local);

        Set<String> escapingObjects = new HashSet<>();

        for (Unit u : body.getUnits()) {
            // Check for return statements
            if (u instanceof ReturnStmt) {
                Value returnValue = ((ReturnStmt) u).getOp();
                if (returnValue instanceof Local) {
                    escapingObjects.add(returnValue.toString());
                }
            }
            

            // Identity statements for parameters
            else if (u instanceof IdentityStmt) {
                IdentityStmt stmt = (IdentityStmt) u;
                if (stmt.getRightOp() instanceof ParameterRef || stmt.getRightOp() instanceof ThisRef) { 
                    escapingObjects.add(stmt.getLeftOp().toString());
                }
            }

            else if (u instanceof JAssignStmt) {
            JAssignStmt stmt = (JAssignStmt) u;
            Value lhs = stmt.getLeftOp();
            Value rhs1 = stmt.getRightOp();
            if (lhs instanceof StaticFieldRef) {
                Value rhs = stmt.getRightOp();
                if (rhs instanceof Local) {
                    escapingObjects.add(rhs.toString());
                }
            }

            if (lhs instanceof Local && rhs1 instanceof VirtualInvokeExpr) {
                VirtualInvokeExpr virtualInvokeExpr = (VirtualInvokeExpr) rhs1;
                String baseReference = virtualInvokeExpr.getBase().toString();
                // if (baseReference.startsWith("$")) {
                    escapingObjects.add(baseReference);
                // }
            }
            }

            else if (u instanceof Stmt) { //System.out.println(u);
            Stmt stmt = (Stmt) u;
                if (stmt.containsInvokeExpr()) {
                    InvokeExpr invokeExpr = stmt.getInvokeExpr();
                    if (invokeExpr instanceof VirtualInvokeExpr) {
                        VirtualInvokeExpr virtualInvokeExpr = (VirtualInvokeExpr) invokeExpr;
                        String baseReference = virtualInvokeExpr.getBase().toString();
                        // if (baseReference.startsWith("$")) {
                            escapingObjects.add(baseReference);
                        // }
                    }
                }
            // if (stmt.containsInvokeExpr()) {
            //     InvokeExpr invokeExpr = stmt.getInvokeExpr();
            //     for (Value arg : invokeExpr.getArgs()) {
            //         if (arg instanceof Local) {
            //             escapingObjects.add(arg.toString());
            //         }
            //     }
            // }

                else if (u instanceof ThrowStmt) {//System.out.println(u);
                    ThrowStmt throwStmt = (ThrowStmt) u;
                    String thrownObject = throwStmt.getOp().toString();
                    escapingObjects.add(thrownObject);
                }

            }

        }

        //System.out.println("Initial Escaping objects: " + escapingObjects);

        Stack<String> stack = new Stack<>();
        stack.addAll(escapingObjects); // Initialize stack with known escaping objects
        //System.out.println(stack);
        while (!stack.isEmpty()) {
            //String current = stack.pop();
            Set<String> currentSet = stackGraph.get(stack.pop());
            if(!currentSet.isEmpty()){
            //For each object, look in the heapGraph for objects it points to
            for(String current : currentSet){
                for (Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> entry : heapGraph.entrySet()) {
                    if (entry.getKey().getKey().equals(current)) { // Object is a field of the current escaping object
                        for (String pointedObject : entry.getValue()) {
                                String pointedObject1=null;
                            for(Map.Entry<String, Set<String>> s_entry : stackGraph.entrySet())
                            {   
                                for(String s_obj : s_entry.getValue())
                                {   
                                    if(s_obj.equals(pointedObject))
                                    {
                                        pointedObject1=s_entry.getKey();
                                        
                                    
                                    }
                                }
                                if(!escapingObjects.contains(pointedObject1) && pointedObject1!=null){
                                    escapingObjects.add(pointedObject1);
                                    stack.push(pointedObject1); // Add new escaping object for further exploration
                                }
                            }
                            
                            
                        }
                    }
                }
            }   
        }
        }
        Set<String> tempList= new HashSet<>();
        for(String e_o:escapingObjects){
        for(String obj : stackGraph.get(e_o)){
                for(Map.Entry<String, Set<String>> s_entry : stackGraph.entrySet()){
                    for(String s_obj : s_entry.getValue()){
                        if(s_obj.equals(obj) && !escapingObjects.contains(s_entry.getKey()))
                        {
                            tempList.add(s_entry.getKey());
                        }
                    }
                }
            }
        }

        escapingObjects.addAll(tempList);
        List<Local> nonEscapingLocals = new ArrayList<>(locals);
        //System.out.println(nonEscapingLocals);
        nonEscapingLocals.removeIf(l -> escapingObjects.contains(l.getName()));
        // System.out.println(escapingObjects);
        // System.out.println(nonEscapingLocals);

        // Get the callgraph 
        UnitGraph cfg = new BriefUnitGraph(body);
        // Get live local using Soot's exiting analysis
        LiveLocals liveLocals = new SimpleLiveLocals(cfg);
        // Units for the body
        PatchingChain<Unit> units = body.getUnits();
        // System.out.println("\n----- " + body.getMethod().getName() + "-----");
        for (Unit u : units) {
            // if (u instanceof JAssignStmt) {//System.out.println(u);
            //     JAssignStmt stmt = (JAssignStmt) u;
            //     Value rhs = stmt.getRightOp();
            //     Value lhs = stmt.getLeftOp();
            //     if(locals.contains(lhs) && locals.contains(rhs)){
            //         System.out.println(u);
            //         continue;
            //     }
            // }
            int flag=0;
            // System.out.println("Unit: " + u);
            List<Local> before = new ArrayList<> (liveLocals.getLiveLocalsBefore(u));
            List<Local> after = new ArrayList<> (liveLocals.getLiveLocalsAfter(u));
            // System.out.println("Live locals before: " + before);
            // System.out.println("Live locals after: " + after);

            if(before.isEmpty() && after.isEmpty()){flag=1;}
            before.removeAll(after);
            for(Local l:nonEscapingLocals){
                if(before.contains(l)){
                    Set<String> born_line= stackGraph.get(l.toString());
                    // Set<String> temp= new HashSet<>();
                    for(String b_l: born_line){//System.out.println("ddddddd");
                        if(b_l!="null"){
                        Dead.put(b_l,String.valueOf(u.getJavaSourceStartLineNumber()));
                        // System.out.println(Dead);
                        // temp.add(b_l);
                        // System.out.println("Dead at " + u.getJavaSourceStartLineNumber());
                        recur(b_l,stackGraph,heapGraph,u.getJavaSourceStartLineNumber());
                        // for(String r: temp){System.out.println(temp);
                        // for(Map.Entry<AbstractMap.SimpleEntry<String,String>,Set<String>> e : heapGraph.entrySet()){
                        //     if(r.equals(e.getKey().getKey()) )
                        //     {   
                        //         for(String s: e.getValue()){
                        //             //int f=0;
                        //             // for(Map.Entry<String,Set<String>> e1 : stackGraph.entrySet()){
                        //             //     if(e1.getValue().contains(s)){
                        //             //         f=1;
                        //             //     }
                        //             // }
                        //            // if(f==0){
                        //                 System.out.println("fffffffff");
                        //                 Dead.put(s,String.valueOf(u.getJavaSourceStartLineNumber()));
                        //                 temp.add(s);
                        //                 System.out.println(Dead.get(s));
                        //                 System.out.println("Dead at " + u.getJavaSourceStartLineNumber());
                        //             //}
                        //         }
                        //     }
                        //     }
                        // }
                        // System.out.println(temp);
                        // System.out.println("Live locals before: " + before);
                        // System.out.println("Live locals after: " + after);
                        // System.out.println();
                    }
                    }
                }
            }
            if(flag==1){
                if (u instanceof Stmt) {
                    Stmt stmt = (Stmt) u;
                    if (stmt.containsInvokeExpr()) {
                        if (stmt instanceof AssignStmt) {
                            AssignStmt assignStmt = (AssignStmt) u;
                            Value leftOp=assignStmt.getLeftOp();
                            Set<String> born_line= stackGraph.get(leftOp.toString());
                            Set<String> temp= new HashSet<>();
                            for(String b_l: born_line){//System.out.println("ccccccc");
                            if(b_l!="null"){
                                Dead.put(b_l,String.valueOf(u.getJavaSourceStartLineNumber()));
                                // System.out.println(Dead);
                                // temp.add(b_l);
                                // System.out.println("Dead at " + u.getJavaSourceStartLineNumber());
                                recur(b_l,stackGraph,heapGraph,u.getJavaSourceStartLineNumber());

                                // for(String r: temp){System.out.println(temp);
                                // for(Map.Entry<AbstractMap.SimpleEntry<String,String>,Set<String>> e : heapGraph.entrySet()){
                                //     if(r.equals(e.getKey().getKey()) )
                                //     {   
                                //         for(String s: e.getValue()){
                                //             // int f=0;
                                //             // for(Map.Entry<String,Set<String>> e1 : stackGraph.entrySet()){
                                //             //     if(e1.getValue().contains(s)){
                                //             //         f=1;
                                //             //     }
                                //             // }
                                //             // if(f==0){
                                //                 System.out.println("JJJJJJJJJ");
                                //                 Dead.put(s,String.valueOf(u.getJavaSourceStartLineNumber()));
                                //                 temp.add(s);
                                //                 System.out.println(Dead.get(s));
                                //                 System.out.println("Dead at " + u.getJavaSourceStartLineNumber());
                                //             //}
                                //         }
                                //     }
                                //  }
                                // }
                                // System.out.println("Live locals before: " + before);
                                // System.out.println("Live locals after: " + after);
                                // System.out.println();
                            }
                            }
                        }
                    }
                }
            }
        
        }

        Set<String> lns_of_nonEsc = new HashSet<>();
        if(!nonEscapingLocals.isEmpty()){//System.out.println(nonEscapingLocals);
        for(Local nonEsc : nonEscapingLocals){ 
            for( String l: stackGraph.get(nonEsc.toString())){//System.out.println("VVVVVVVVVVVVVVVV");
                lns_of_nonEsc.add(l);
            }
            stackGraph.remove(nonEsc.getName());
            
        }
        }

        for(String n_l:lns_of_nonEsc){
            Iterator<Map.Entry<AbstractMap.SimpleEntry<String,String>,Set<String>>> iterator = heapGraph.entrySet().iterator();
            while(iterator.hasNext())
            {
                Map.Entry<AbstractMap.SimpleEntry<String,String>,Set<String>> entry= iterator.next();
                if(entry.getKey().getKey().equals(n_l))
                iterator.remove();
            }
        }

        // System.out.println("#############removed");

        // System.out.println("Stack Graph:");
        // for (Map.Entry<String, Set<String>> entry : stackGraph.entrySet()) {
        //     String key = entry.getKey();
        //     Set<String> values = entry.getValue();
        //     System.out.println(key + " -> " + values);
        // }

        // System.out.println("Heap Graph:");
        // for (Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> entry : heapGraph.entrySet()) {
        //     AbstractMap.SimpleEntry<String, String> key = entry.getKey();
        //     Set<String> values = entry.getValue();
        //     System.out.println("(" + key.getKey() + ", " + key.getValue() + ") -> " + values);
        // }

        TreeMap<String,String> Dead1=new TreeMap<>(Dead);
        Dead.clear();
        //System.out.println("finished"+method.toString());
        String k = ""+method.getDeclaringClass()+":"+method.getName();
        // System.out.println("Answer:"+Dead1);

        Answer.put(k,Dead1);

        
    }



    private static Pair<Map<String, Set<String>>, Map<AbstractMap.SimpleEntry<String, String>, Set<String>>, LinkedHashMap<String,String>,Set<String> > getlistofMethods(SootMethod method, Set<SootMethod> reachableMethods,LinkedHashMap<String,String> map_context) {
       
        
        // Avoid revisiting methods
        // if (reachableMethods.contains(method)) {
        //     return;
        // }
        // Add the method to the reachable set
        reachableMethods.add(method);
        Set<String> return_ctx=new HashSet<>();
        Pair<Map<String, Set<String>>, Map<AbstractMap.SimpleEntry<String, String>, Set<String>>, LinkedHashMap<String,String>,Set<String> > p;
        // Iterate over the edges originating from this method
       LinkedHashMap<String,String> Caller_ctx=new LinkedHashMap<>();
       
       LinkedHashMap<String,String> temp_ctx=new LinkedHashMap<>();

        Body body = method.getActiveBody();

        Map<String, Set<String>> stackGraph = new HashMap<>();
        Map<AbstractMap.SimpleEntry<String, String>, Set<String>> heapGraph = new HashMap<>();

        PatchingChain<Unit> units = body.getUnits();
        
        // System.out.println("\n--------------------- " + body.getMethod().getName() + "---------------");
        // for(Unit u: units){
        //     System.out.println(u);
        // }
        for (Unit u : units) {//System.out.println(u);
            if (u instanceof JAssignStmt) {//System.out.println(u);
                JAssignStmt stmt = (JAssignStmt) u;
                Value rhs = stmt.getRightOp();
                Value lhs = stmt.getLeftOp();
                

                if (rhs instanceof JNewExpr) {
                    //System.out.println("VVVVVVVVVVVVVVVVVVVVVVVVVV");
                        // Add some points-to relationships to the graph
                        String key=lhs.toString();
                        String s=""+u.getJavaSourceStartLineNumber();
                                                
                        stackGraph.computeIfAbsent(key, k -> new HashSet<>()).add(s);
                        //System.out.println(stackGraph.get(key));
                        //System.out.println(key+" "+stackGraph.get(key));

                       // System.out.println("Unit is " + u + " and the line number is : " + u.getJavaSourceStartLineNumber());
                    
                }

                else if(lhs instanceof FieldRef)
                {   //System.out.println("zzzzzzz");
                    String line= u.toString();
                    Pattern pattern = Pattern.compile("(\\$\\w+|\\w+)\\.<[^:]+: \\w+ (\\w+)>\\s*=\\s*(\\$\\w+|\\w+)");
                    Matcher matcher = pattern.matcher(line);
                    
                    String key=null;
                    String field=null;
                    String var2=null;
                    // Check if the pattern matches and extract the groups
                    if (matcher.find()) {
                        key = matcher.group(1);
                        field = matcher.group(2);
                        var2 = matcher.group(3);
                    }
                    // System.out.println(""+key+""+field+""+var2);
                    Set<String> objs;
                    Set<String> dests= stackGraph.get(var2);
                    if((objs=stackGraph.get(key))!=null)
                    {   for(String obj : objs){
                            for(String dest : dests){
                                AbstractMap.SimpleEntry<String, String> mapKey = new AbstractMap.SimpleEntry<>(obj, field);
                                heapGraph.computeIfAbsent(mapKey, k -> new HashSet<>()).add(dest);
                                
                                Set<String> value=heapGraph.get(mapKey);
                               // System.out.println("(" + mapKey.getKey() + ", " + mapKey.getValue() + ") --> " + value);
                            }
                    }

                    }
                    
                }

                else if(rhs instanceof FieldRef)
                {
                    String line= u.toString();
                    Pattern pattern = Pattern.compile("(\\$\\w+|\\w+)\\s*=\\s*(\\$\\w+|\\w+)\\.<[^:]+: \\w+ (\\w+)>");
                    Matcher matcher = pattern.matcher(line);
                    
                    String key=null;
                    String var2=null;
                    String field=null;
                   
                    // Check if the pattern matches and extract the groups
                    if (matcher.find()) {
                        key = matcher.group(1);
                        var2 = matcher.group(2);
                        field = matcher.group(3);
                        
                    }

                    Set<String> i_values=stackGraph.get(var2);
                    
                    for(String i_value : i_values){
                    Set<String> objs;
                    AbstractMap.SimpleEntry<String, String> mapKey = new AbstractMap.SimpleEntry<>(i_value, field);
                    if((objs=heapGraph.get(mapKey))!=null){
                        for(String obj : objs){
                        stackGraph.computeIfAbsent(key, k -> new HashSet<>()).add(obj);
                        }
                    }

                    else
                    {
                        Set<String> dummy_obj=stackGraph.get(var2);
                        for(String obj: dummy_obj)
                        {   Integer parsedInt=Integer.parseInt(obj);
                            if(parsedInt<1){
                                Integer pi=parsedInt-1;
                                String dummy_obj_referencing_obj = String.valueOf(pi);
                                AbstractMap.SimpleEntry<String, String> map_Key = new AbstractMap.SimpleEntry<>(obj, field);
                                heapGraph.computeIfAbsent(map_Key, k -> new HashSet<>()).add(dummy_obj_referencing_obj);
                            }    
                            else{
                                AbstractMap.SimpleEntry<String, String> map_Key = new AbstractMap.SimpleEntry<>(obj, field);
                                heapGraph.computeIfAbsent(map_Key, k -> new HashSet<>()).add("null");
                            }
                        }

                        if((objs=heapGraph.get(mapKey))!=null){
                            for(String obj : objs){
                            stackGraph.computeIfAbsent(key, k -> new HashSet<>()).add(obj);
                            }
                        }
                    }
                    }
                    //System.out.println(key+" "+stackGraph.get(key));
                }

                else if(lhs instanceof Local && rhs instanceof Local)
                {
                    String key=lhs.toString();
                    Set<String> objs=stackGraph.get(rhs.toString());
                    for(String obj: objs)
                    stackGraph.computeIfAbsent(key, k -> new HashSet<>()).add(obj);

                }
            }

            if (u instanceof ReturnStmt) {
                Value returnValue = ((ReturnStmt) u).getOp();
                return_ctx=stackGraph.get(returnValue.toString());
            }

            if (u instanceof Stmt) {
                Stmt stmt = (Stmt) u;
                if (stmt.containsInvokeExpr()) {
                    LinkedHashMap<String,String> Callee_ctx=new LinkedHashMap<>();
                    if (stmt instanceof AssignStmt) {
                        AssignStmt assignStmt = (AssignStmt) u;
                        Value leftOp=assignStmt.getLeftOp();
                        Set<String> r_ctx=new HashSet<>(); 
                        InvokeExpr invokeExpr = stmt.getInvokeExpr();
                        if (invokeExpr instanceof StaticInvokeExpr) {
                            StaticInvokeExpr staticInvoke = (StaticInvokeExpr) invokeExpr;
                            SootMethod invokedMethod = staticInvoke.getMethod();
                            for (Value arg : invokeExpr.getArgs()) {
                                // if (arg instanceof Local) {
                                //     escapingObjects.add(arg.toString());
                                // }
                                String key=arg.toString();
                                for(String v : stackGraph.get(key)){
                                Callee_ctx.put(key,v);
                                break;
                                }
                            }

                            if (!invokedMethod.isJavaLibraryMethod()) { //System.out.println("oooooooooooo");
                                p=getlistofMethods(invokedMethod, reachableMethods,Callee_ctx);
                                Map<String, Set<String>> Sgraph=p.getKey();
                                Map<AbstractMap.SimpleEntry<String, String>, Set<String>> Hgraph=p.getValue();
                                LinkedHashMap<String,String> up_Caller_ctx=p.getmap_ctx();
                                r_ctx=p.getreturn_ctx();
                                //System.out.println("updated:"+ up_Caller_ctx);
                                // if(!up_Caller_ctx.isEmpty()){
                                    LinkedHashMap<Set<String>,Set<String>> up_val=new LinkedHashMap<>();
                                    Iterator<Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>>> itr2 = Hgraph.entrySet().iterator();
                                    Map<AbstractMap.SimpleEntry<String, String>, Set<String>> entriesToRemove = new HashMap<>();
                                    Map<AbstractMap.SimpleEntry<String, String>, Set<String>> entriesToAdd = new HashMap<>();
                                    // System.out.println("Hgraph:"+Hgraph);
                                    while(itr2.hasNext()){
                                        Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> e2=itr2.next();
                                        String k1=e2.getKey().getKey();
                                        String v1=e2.getKey().getValue();
                                        Set<String> values= e2.getValue();
                                        String real_obj= up_Caller_ctx.get(k1);
                                        
                                        // System.out.println(r_ctx);
                                        if(r_ctx.contains(k1) && Integer.parseInt(k1)>0){
                                            AbstractMap.SimpleEntry<String, String> mapKey = new AbstractMap.SimpleEntry<>(k1,v1);
                                            entriesToAdd.put(mapKey,values);
                                        }
                                        if(real_obj!=null){
                                            int flag=0;
                                            Iterator<Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>>> itr1 = heapGraph.entrySet().iterator();
                                            while(itr1.hasNext()){
                                                Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> e1=itr1.next();
                                                AbstractMap.SimpleEntry<String, String> mapKey1 = new AbstractMap.SimpleEntry<>(real_obj,v1);
                                                if(e1.getKey().equals(mapKey1)){ flag=1;
                                                    entriesToRemove.put(e1.getKey(),e1.getValue());
                                                    Set<String> up_key= e1.getValue();
                                                    for(String val:values){
                                                        AbstractMap.SimpleEntry<String, String> mapKey = new AbstractMap.SimpleEntry<>(real_obj,v1);
                                                        entriesToAdd.computeIfAbsent(mapKey, k -> new HashSet<>()).add(val);
                                                        if(!up_key.contains(null) && val!=null)
                                                        up_val.computeIfAbsent(up_key,k->new HashSet<>()).add(val);
                                                    }
                                                }
                                            }
                                            if(flag==0){
                                                AbstractMap.SimpleEntry<String, String> mapKey = new AbstractMap.SimpleEntry<>(real_obj,v1);
                                                entriesToAdd.put(mapKey,e2.getValue());
                                            }
                                        }

                                    }
                                    // System.out.println("UP_VAL:"+up_val);
                                    for (Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> entry : entriesToRemove.entrySet()) {
                                        heapGraph.remove(entry.getKey());
                                        }
                                        // System.out.println("kkkkkk"+entriesToAdd);
                                    heapGraph.putAll(entriesToAdd);

                                    for(Map.Entry<Set<String>,Set<String>> e: up_val.entrySet()){
                                        Set<String> st=e.getValue();
                                        for(String s :st){

                                            if(Integer.parseInt(s)<0){
                                                up_val.put(e.getValue(),e.getKey());
                                                up_val.remove(e.getKey());
                                            }

                                        }
                                    }

                                    for(Map.Entry<Set<String>,Set<String>> e: up_val.entrySet()){
                                        for(Map.Entry<String,Set<String>> e1 : stackGraph.entrySet()){
                                            if(!e.getKey().contains("null") && e1.getValue().equals(e.getKey())){
                                                e1.setValue(e.getValue());
                                            }
                                        }

                                        for(Map.Entry<AbstractMap.SimpleEntry<String,String>,Set<String>> e2: heapGraph.entrySet()){
                                            if(!e.getKey().contains("null") && e2.getValue().equals(e.getKey())){
                                                e2.setValue(e.getValue());
                                            }
                                        }
                                    }
                                // }
                            }
                            
                        }
                        
                        stackGraph.put(leftOp.toString(),r_ctx);

                    }

                    else{
                        InvokeExpr invokeExpr = stmt.getInvokeExpr();
                        if (invokeExpr instanceof StaticInvokeExpr) {
                            StaticInvokeExpr staticInvoke = (StaticInvokeExpr) invokeExpr;
                            SootMethod invokedMethod = staticInvoke.getMethod();
                            for (Value arg : invokeExpr.getArgs()) {
                                // if (arg instanceof Local) {
                                //     escapingObjects.add(arg.toString());
                                // }
                                String key=arg.toString();
                                for(String v : stackGraph.get(key)){
                                Callee_ctx.put(key,v);
                                break;
                                }
                            }

                            if (!invokedMethod.isJavaLibraryMethod()) {//System.out.println("LLLLLLLL");
                                p=getlistofMethods(invokedMethod, reachableMethods,Callee_ctx);
                                Map<String, Set<String>> Sgraph=p.getKey();
                                Map<AbstractMap.SimpleEntry<String, String>, Set<String>> Hgraph=p.getValue();
                                LinkedHashMap<String,String> up_Caller_ctx=p.getmap_ctx();
                                // System.out.println("updated:"+ up_Caller_ctx);
                                if(!up_Caller_ctx.isEmpty()){
                                    LinkedHashMap<Set<String>,Set<String>> up_val=new LinkedHashMap<>();
                                    Iterator<Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>>> itr2 = Hgraph.entrySet().iterator();
                                    Map<AbstractMap.SimpleEntry<String, String>, Set<String>> entriesToRemove = new HashMap<>();
                                    Map<AbstractMap.SimpleEntry<String, String>, Set<String>> entriesToAdd = new HashMap<>();
                                    // System.out.println("Hgraph:"+Hgraph);
                                    while(itr2.hasNext()){
                                        Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> e2=itr2.next();
                                        String k1=e2.getKey().getKey();
                                        String v1=e2.getKey().getValue();
                                        Set<String> values= e2.getValue();
                                        String real_obj= up_Caller_ctx.get(k1);
                                        int flag=0;
                                        Iterator<Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>>> itr1 = heapGraph.entrySet().iterator();
                                        while(itr1.hasNext()){
                                            Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> e1=itr1.next();
                                            AbstractMap.SimpleEntry<String, String> mapKey1 = new AbstractMap.SimpleEntry<>(real_obj,v1);
                                            if(e1.getKey().equals(mapKey1)){ flag=1;
                                                entriesToRemove.put(e1.getKey(),e1.getValue());
                                                Set<String> up_key= e1.getValue();
                                                for(String val:values){
                                                    AbstractMap.SimpleEntry<String, String> mapKey = new AbstractMap.SimpleEntry<>(real_obj,v1);
                                                    entriesToAdd.computeIfAbsent(mapKey, k -> new HashSet<>()).add(val);
                                                    if(!up_key.contains(null) && val!=null)
                                                    up_val.computeIfAbsent(up_key,k->new HashSet<>()).add(val);
                                                }
                                            }
                                        }
                                        if(flag==0){
                                            AbstractMap.SimpleEntry<String, String> mapKey = new AbstractMap.SimpleEntry<>(real_obj,v1);
                                            entriesToAdd.put(mapKey,e2.getValue());
                                        }

                                    }
                                    // System.out.println("UP_VAL:"+up_val);
                                    for (Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> entry : entriesToRemove.entrySet()) {
                                        heapGraph.remove(entry.getKey());
                                        }

                                        
                                    heapGraph.putAll(entriesToAdd);

                                    for(Map.Entry<Set<String>,Set<String>> e: up_val.entrySet()){
                                        for(Map.Entry<String,Set<String>> e1 : stackGraph.entrySet()){
                                            if(!e.getKey().contains("null") && e1.getValue().equals(e.getKey())){
                                                e1.setValue(e.getValue());
                                            }
                                        }

                                        for(Map.Entry<AbstractMap.SimpleEntry<String,String>,Set<String>> e2: heapGraph.entrySet()){
                                            if(!e.getKey().contains("null") && e2.getValue().equals(e.getKey())){
                                                e2.setValue(e.getValue());
                                            }
                                        }
                                    }
                                }
                            }
                            
                        }

                        if (invokeExpr instanceof VirtualInvokeExpr) {
                            
                            VirtualInvokeExpr virtualInvokeExpr = (VirtualInvokeExpr) invokeExpr;
                            SootMethod invokedMethod = virtualInvokeExpr.getMethod();
                            Value base = virtualInvokeExpr.getBase();
                            for(String s:stackGraph.get(base.toString())){
                                Callee_ctx.put(base.toString(),s);
                                break;
                            }
                            for (Value arg : virtualInvokeExpr.getArgs()) {
                                String key=arg.toString();
                                for(String v : stackGraph.get(key)){
                                Callee_ctx.put(key,v);
                                break;
                                }
                            }
                            if (!invokedMethod.isJavaLibraryMethod()) { //System.out.println("oooooooooooo");
                                p=getlistofMethods(invokedMethod, reachableMethods,Callee_ctx);
                                Map<String, Set<String>> Sgraph=p.getKey();
                                Map<AbstractMap.SimpleEntry<String, String>, Set<String>> Hgraph=p.getValue();
                                LinkedHashMap<String,String> up_Caller_ctx=p.getmap_ctx();
                                // System.out.println("updated:"+ up_Caller_ctx);
                                if(!up_Caller_ctx.isEmpty()){
                                    LinkedHashMap<Set<String>,Set<String>> up_val=new LinkedHashMap<>();
                                    Iterator<Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>>> itr2 = Hgraph.entrySet().iterator();
                                    Map<AbstractMap.SimpleEntry<String, String>, Set<String>> entriesToRemove = new HashMap<>();
                                    Map<AbstractMap.SimpleEntry<String, String>, Set<String>> entriesToAdd = new HashMap<>();
                                    // System.out.println("Hgraph:"+Hgraph);
                                    while(itr2.hasNext()){
                                        Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> e2=itr2.next();
                                        String k1=e2.getKey().getKey();
                                        String v1=e2.getKey().getValue();
                                        Set<String> values= e2.getValue();
                                        String real_obj= up_Caller_ctx.get(k1);
                                        int flag=0;
                                        Iterator<Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>>> itr1 = heapGraph.entrySet().iterator();
                                        while(itr1.hasNext()){
                                            Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> e1=itr1.next();
                                            AbstractMap.SimpleEntry<String, String> mapKey1 = new AbstractMap.SimpleEntry<>(real_obj,v1);
                                            if(e1.getKey().equals(mapKey1)){ flag=1;
                                                entriesToRemove.put(e1.getKey(),e1.getValue());
                                                Set<String> up_key= e1.getValue();
                                                for(String val:values){
                                                    AbstractMap.SimpleEntry<String, String> mapKey = new AbstractMap.SimpleEntry<>(real_obj,v1);
                                                    entriesToAdd.computeIfAbsent(mapKey, k -> new HashSet<>()).add(val);
                                                    if(!up_key.contains(null) && val!=null)
                                                    up_val.computeIfAbsent(up_key,k->new HashSet<>()).add(val);
                                                }
                                            }
                                        }
                                        if(flag==0){
                                            AbstractMap.SimpleEntry<String, String> mapKey = new AbstractMap.SimpleEntry<>(real_obj,v1);
                                            entriesToAdd.put(mapKey,e2.getValue());
                                        }

                                    }
                                    // System.out.println("UP_VAL:"+up_val);
                                    for (Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> entry : entriesToRemove.entrySet()) {
                                        heapGraph.remove(entry.getKey());
                                        }

                                        
                                    heapGraph.putAll(entriesToAdd);

                                    for(Map.Entry<Set<String>,Set<String>> e: up_val.entrySet()){
                                        for(Map.Entry<String,Set<String>> e1 : stackGraph.entrySet()){
                                            if(!e.getKey().contains("null") && e1.getValue().equals(e.getKey())){
                                                e1.setValue(e.getValue());
                                            }
                                        }

                                        for(Map.Entry<AbstractMap.SimpleEntry<String,String>,Set<String>> e2: heapGraph.entrySet()){
                                            if(!e.getKey().contains("null") && e2.getValue().equals(e.getKey())){
                                                e2.setValue(e.getValue());
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }


            if(u instanceof IdentityStmt){//System.out.println(u);
                
                IdentityStmt stmt = (IdentityStmt) u;
                Value rhs = stmt.getRightOp();
                Value lhs = stmt.getLeftOp();

                if(rhs instanceof ParameterRef){//System.out.println(u);
                    //System.out.println("VVVVVVVVVVVVpppppppppppp");
                    String line = u.toString();

                    // Define the regex pattern to match the parameter and capture its index
                    Pattern pattern = Pattern.compile("@parameter(\\d+)");
                    Matcher matcher = pattern.matcher(line);

                    // Check if the pattern matches and extract the captured group
                    if (matcher.find()) {
                        Integer parameterIndex = Integer.parseInt(matcher.group(1)) -method.getParameterCount();  // Group 1 contains the index
                        String key=lhs.toString();
                        String s=""+parameterIndex;
                
                        stackGraph.computeIfAbsent(key, k -> new HashSet<>()).add(s);
                        temp_ctx.put(key,s);

                        //System.out.println(key+" "+stackGraph.get(key));
                    } 
                }

                else if(rhs instanceof ThisRef)
                {   //System.out.println(u);
                    //System.out.println("VVVVVVVVVVVVtttttttttttt");
                    String key=lhs.toString();
                    String s="0";
                    stackGraph.computeIfAbsent(key, k -> new HashSet<>()).add(s);
                    
                }
            }
        }

        Iterator<Map.Entry<String, String>> it1 = map_context.entrySet().iterator();
        Iterator<Map.Entry<String, String>> it2 = temp_ctx.entrySet().iterator();

        while (it1.hasNext() && it2.hasNext()) {
            Map.Entry<String, String> entry1 = it1.next();
            Map.Entry<String, String> entry2 = it2.next();
            
            String key1 = entry1.getKey();
            String value1 = entry1.getValue();
            
            String key2 = entry2.getKey();
            String value2 = entry2.getValue();
            
            Caller_ctx.put(value2,value1);
    
        }


        // System.out.println("Stack Graph:");
        // for (Map.Entry<String, Set<String>> entry : stackGraph.entrySet()) {
        //     String key = entry.getKey();
        //     Set<String> values = entry.getValue();
        //     System.out.println(key + " -> " + values);
        // }

        // System.out.println("Heap Graph:");
        // for (Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> entry : heapGraph.entrySet()) {
        //     AbstractMap.SimpleEntry<String, String> key = entry.getKey();
        //     Set<String> values = entry.getValue();
        //     System.out.println("(" + key.getKey() + ", " + key.getValue() + ") -> " + values);
        // }


        // System.out.println(">>>>>>>>>>>"+method.toString());

        // System.out.println("Stack Graph:");
        // for (Map.Entry<String, Set<String>> entry : stackGraph.entrySet()) {
        //     String key = entry.getKey();
        //     Set<String> values = entry.getValue();
        //     System.out.println(key + " -> " + values);
        // }

        // System.out.println("Heap Graph:");
        // for (Map.Entry<AbstractMap.SimpleEntry<String, String>, Set<String>> entry : heapGraph.entrySet()) {
        //     AbstractMap.SimpleEntry<String, String> key = entry.getKey();
        //     Set<String> values = entry.getValue();
        //     System.out.println("(" + key.getKey() + ", " + key.getValue() + ") -> " + values);
        // }
        processCFG(method,stackGraph,heapGraph);//,method.getParameterCount()
        

        return Pair.of(stackGraph, heapGraph,Caller_ctx,return_ctx);
    
        
    }

    public static void printAnswer(){
        for(Map.Entry<String,TreeMap<String,String>> e : Answer.entrySet()){
            System.out.print(e.getKey()+" ");
            for(Map.Entry<String,String> ime : e.getValue().entrySet()){
                System.out.print(ime.getKey()+":"+ime.getValue()+" ");
            }
            System.out.println();
        }
    }
}

