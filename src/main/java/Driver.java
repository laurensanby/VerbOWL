
import java.io.File;
import java.io.IOException;
import java.util.Collections;
import java.util.Set;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.*;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/**
 *
 * @author Lauren
 */
public class Driver {
    
    static int count, subClassCount, disjointCount, owlThingCount;
    static NodeList constraints;
    
    public static void main(String[] args){
        // TODO code application logic here
        count=0;
        subClassCount=0;
        disjointCount=0;
        owlThingCount=0;
        try
        {
            File f = new File("C:\\Users\\Lauren\\Documents\\UCT\\Honours\\project\\AfricanWildlifeOntology1.owl");
            OWLOntologyManager m = OWLManager.createOWLOntologyManager();
            OWLOntology o = m.loadOntologyFromOntologyDocument(f);
            constraints = readXML("template_v1.xml");
                       
            //walker
            OWLOntologyWalker walker = new OWLOntologyWalker(Collections.singleton(o));
            OWLOntologyWalkerVisitor visitor;
            visitor = new OWLOntologyWalkerVisitor(walker){
                @Override
                public void visit(OWLEquivalentClassesAxiom axiom) {
                    /*OWLAxiom axiom1 = getCurrentAxiom();
                    System.out.println("!!-->"+axiom1);
                    Set<OWLEquivalentClassesAxiom> s1 = axiom.asPairwiseAxioms();
                    for (OWLEquivalentClassesAxiom e : s1)
                    {
                    System.out.println("--"+e);
                    }
                    Set<OWLClassExpression> s = axiom.getNestedClassExpressions();
                    for (OWLClassExpression a : s)
                    {
                    
                    System.out.println("!!"+a);
                    }*/
                }
                
                @Override
                public void visit(OWLObjectSomeValuesFrom desc) {
                    OWLAxiom axiom = getCurrentAxiom();
                    //System.out.println(axiom.toString().toUpperCase());
                }
                
                @Override
                public void visit(OWLDisjointClassesAxiom axiom) {
                    count++;
                    disjointCount++;
                    Set<OWLDisjointClassesAxiom> classes = axiom.asPairwiseAxioms();
                    Set<OWLClassExpression> literals;
                    String[] objects = new String[2];
                    int i=0;
                    for (OWLDisjointClassesAxiom c : classes)
                    {
                        i=0;
                        literals = c.getNestedClassExpressions();
                        for (OWLClassExpression l : literals)
                        {
                            objects[i] = getName(l+"");
                            i++;
                        }
                        System.out.print("Disjoint ");
                        
                        printSentence(objects, null, "Disjoint");
                    }
                }
         
                @Override
                public void visit(OWLSubClassOfAxiom sub) {
                    String subClass = sub.getSubClass().toString();
                    OWLClassExpression superClassExpr = sub.getSuperClass();             
                    String superClass = superClassExpr.toString();
                    if(superClassExpr.isClassExpressionLiteral())
                    {//CHECK FOR COMPLEMENTS!!
                        if (!(superClassExpr.isOWLThing()))
                        {
                            String[] objects = {
                             getName(subClass),
                             getName(superClass)
                            };
                            System.out.print("Subclass ");
                            count++;
                            subClassCount++;
                            printSentence(objects, null, "OWLSubClassOfAxiom");
                        }
                        else
                        { //Not printing OWLThing
                            owlThingCount++;
                        }
                    }
                          
                    else if (superClassExpr.getClassExpressionType()==ClassExpressionType.OBJECT_SOME_VALUES_FROM)
                    {
                        relationsDL(superClassExpr, subClass+"", "OWLObjectSomeValuesFrom");                       
                    }
                    else if (superClassExpr.getClassExpressionType()==ClassExpressionType.OBJECT_ALL_VALUES_FROM)
                    {
                        relationsDL(superClassExpr, subClass+"", "OWLObjectAllValuesFrom");
                        //System.out.println(sub.getNNF());
                    }
                    else if (superClassExpr.getClassExpressionType()==ClassExpressionType.OBJECT_INTERSECTION_OF)
                    {
                        relationsDL(superClassExpr, subClass+"", "OWLObjectIntersectionOf");
                    }
                }
            
            };
        
            walker.walkStructure(visitor);
         
            //TESTING
            System.out.println("Number of axioms printed: "+count);
            System.out.println("Number subclass: "+subClassCount);
            System.out.println("Number disjoint: "+disjointCount);
        
            int numAxioms = o.getAxiomCount()-o.getAxiomCount(AxiomType.ANNOTATION_ASSERTION) - o.getAxiomCount(AxiomType.DECLARATION)-owlThingCount;
            System.out.println("Number of axioms: "+numAxioms); //TEST
            
            Set<OWLAxiom> a = o.getAxioms();
            for (OWLAxiom ax : a)
            {
                AxiomType type = ax.getAxiomType();
                
                if (!(type.getName().equals("SubClassOf")) && !(type.getName().equals("DisjointClasses")) && !(type.equals(AxiomType.ANNOTATION_ASSERTION)) && !(type.equals(AxiomType.DECLARATION)))
                {
                    System.out.println("!!!"+ax.toString());
                }
            }
            
            System.out.println("Number of subclass: "+(o.getAxiomCount(AxiomType.SUBCLASS_OF)-owlThingCount)); //TEST
            System.out.println("Number of disjoint: "+o.getAxiomCount(AxiomType.DISJOINT_CLASSES)); //TEST
        }
        catch (OWLOntologyCreationException e)
        {
            System.out.println("EXCEPTION CAUGHT "+e);
        }       
    }
    
    public static void relationsDL(OWLClassExpression superClassExpr, String subClass, String type)
    {
        Set<OWLObjectProperty> objProp;
        Set<OWLClassExpression> nested = superClassExpr.getNestedClassExpressions();
        boolean negation = false;
        boolean union = false;
        boolean intersection = false;
        String literals = getName(subClass)+";";
        String roles = "";
        for (OWLClassExpression c : nested)
        {
            c = c.getNNF();
            ClassExpressionType cet = c.getClassExpressionType();
            switch(cet)
            {
            case OBJECT_COMPLEMENT_OF:
                negation = true;
                break;
            case OBJECT_UNION_OF:
                union = true;
                break;
            case OBJECT_INTERSECTION_OF:
                intersection = true;
                break;
            default:
                if (c.isClassExpressionLiteral())
                    literals+=getName(c+"")+";";
                else{
                    objProp = c.getObjectPropertiesInSignature();
                    for (OWLObjectProperty o : objProp)
                    {
                        roles+=getName(o+"")+";";
                    }
                }
                break;
            }
        }
        if (type.equals("OWLObjectAllValuesFrom"))
        {
            roles = roles.replaceFirst("-", ";");
        }
        if (type.equals("OWLObjectIntersectionOf"))
        {
            type = "OWLObjectSomeValuesFrom";
        }
        //if (intersection && all roles are the same)
        System.out.print(type+" ");
        count++;
        subClassCount++;
        printSentence(literals.split(";"),roles.split(";"),type, negation, union, intersection);
    }
    
    public static void printSentence(String[] objects, String[] roles, String type)
    {
        printSentence(objects, roles, type, false, false, false);
    }
     
     public static void printSentence(String[] objects, String[] roles, String type, boolean negation, boolean union, boolean intersection)
     {
        //Choose constraint based on type
        //FIND MORE GENERIC WAY TO DO THIS??
        Node prop = null;
        String cType="";
        for (int j=0; j<constraints.getLength(); j++){
            cType = constraints.item(j).getAttributes().getNamedItem("type").toString();
            if (!negation && !union && !intersection && cType.equals("type=\""+type+"\"") 
                    || (negation && cType.equals("type=\""+type+" negation\""))
                    || (union && cType.equals("type=\""+type+" union\""))
                    || (intersection && cType.equals("type=\""+type+" intersection\"")))
            {
                prop = constraints.item(j);
                break;
            }
        }
        int index;
        NodeList children = prop.getChildNodes();
        Node child;
        if (null != children) {
            for (int i=0; i<children.getLength(); i++)
            {
                child = children.item(i);
                switch (child.getNodeName()) {
                case "Text":
                    System.out.print(child.getTextContent());
                    break;
                case "Object":
                    index = Integer.parseInt(child.getAttributes().getNamedItem("index").getTextContent());
                    System.out.print(objects[index]);
                    break;
                case "Role":
                    index = Integer.parseInt(child.getAttributes().getNamedItem("index").getTextContent());
                    if (index<roles.length)
                    {    System.out.print(roles[index]+" ");    }
                    break;
                case "Loop":
                    index = Integer.parseInt(child.getAttributes().getNamedItem("index").getTextContent());
                    NodeList loopChildren = child.getChildNodes();
                    Node loopChild;
                    while (index<objects.length) {
                        for (int j=0; j<loopChildren.getLength(); j++) {
                            loopChild = loopChildren.item(j);
                            switch (loopChild.getNodeName())
                            {
                            case "Text":
                                System.out.print(loopChild.getTextContent());
                                break;
                            case "Object":
                                System.out.print(objects[index]);
                                break;
                            case "Role":
                                System.out.print(roles[index-1]+" ");
                                break;
                            }
                        }
                        index++;
                    }
                }
            }
        }
        System.out.println();
     }
     
     public static NodeList readXML(String xml) {
        
        Document dom;
        // Make an  instance of the DocumentBuilderFactory
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        try {
            // use the factory to take an instance of the document builder
            DocumentBuilder db = dbf.newDocumentBuilder();
            // parse using the builder to get the DOM mapping of the    
            // XML file
            dom = db.parse(xml);
            NodeList constr = dom.getElementsByTagName("Constraint");
            return constr;

        } catch (ParserConfigurationException | SAXException pce) {
            System.out.println(pce.getMessage());
        } catch (IOException ioe) {
            System.err.println(ioe.getMessage());
        }

        return null;
    }
     
     private static String getName(String literal)
     {
         return literal.substring(literal.indexOf("#")+1,literal.indexOf(">"));
     }
    
}