
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
    static String globalRoles, globalLiterals, globalAndOr, globalNest;
    static NodeList constraints;

    public static void main(String[] args) {
        // TODO code application logic here
        count = 0;
        subClassCount = 0;
        disjointCount = 0;
        owlThingCount = 0;
        try {
            File f = new File("C:\\Users\\Lauren\\Documents\\UCT\\Honours\\project\\Ontologies\\wine.rdf");
            OWLOntologyManager m = OWLManager.createOWLOntologyManager();
            OWLOntology o = m.loadOntologyFromOntologyDocument(f);
            constraints = readXML("template_v1.xml");

            //walker
            OWLOntologyWalker walker = new OWLOntologyWalker(Collections.singleton(o));
            OWLOntologyWalkerVisitor visitor;
            visitor = new OWLOntologyWalkerVisitor(walker) {
                @Override
                public void visit(OWLEquivalentClassesAxiom axiom) {
                    String printString = getPartSentence(getName(axiom.getNamedClasses() + "").split(";"), null, "PartObject", null);
                    Set<OWLSubClassOfAxiom> subClasses = axiom.asOWLSubClassOfAxioms();
                    OWLClassExpression ce = null;
                    for (OWLSubClassOfAxiom subClassOfAxiom : subClasses) {
                        if (subClassOfAxiom.getSubClass().isClassExpressionLiteral()) {
                            ce = subClassOfAxiom.getSuperClass();
                        } else {
                            ce = subClassOfAxiom.getSubClass();
                        }
                        break;
                    }
                    count++;
                    printString += getClassExpression(ce.getNNF());
                    printFullSentence(printString);
//                    OWLAxiom axiom1 = getCurrentAxiom();
//                    System.out.println("!!-->" + axiom1);
//
//                    globalLiterals = getName(axiom.getNamedClasses() + "") + ";";
//                    globalRoles = "";
//                    globalAndOr = "";
//                    globalNest = "";
//                    Set<OWLClassExpression> s = axiom.getNestedClassExpressions();
//                    for (OWLClassExpression a : s) {
//
//                        //System.out.println("!!"+a);
//                        //Set<OWLClassExpression> conjunct;
//
//                        if (a.getClassExpressionType().equals(ClassExpressionType.OBJECT_INTERSECTION_OF)) //or union of
//                        {
//                            nestRecursion(a);
//                            System.out.println("------------");
//        System.out.println(globalLiterals);
//        System.out.println(globalRoles);
//        System.out.println(globalAndOr);
//        System.out.println(globalNest);
//        System.out.println("----------------");
                            /*int setCount = 1;
                     conjunct = a.asConjunctSet();
                     for (OWLClassExpression b : conjunct) {
                     System.out.println("-->" + b);
                     Set<OWLClassExpression> s2 = b.getNestedClassExpressions();
                     if (s2.size() == 2) {
                     ClassExpressionType type = b.getClassExpressionType();
                     switch (type) {
                     case OBJECT_SOME_VALUES_FROM:
                     roles += getName(b.getObjectPropertiesInSignature() + "") + ";";
                     literals += getName(b.getClassesInSignature() + "") + ";";
                     if (setCount < conjunct.size()) {
                     andOr += "en;";
                     }
                     nest += "false;";
                     System.out.println(getName(b.getObjectPropertiesInSignature() + ""));
                     System.out.println(getName(b.getClassesInSignature() + ""));
                            
                     break;
                     case OBJECT_ALL_VALUES_FROM:
                     break;
                            
                     }
                     } else {
                     for (OWLClassExpression a2 : s2) {
                     a2.asConjunctSet();
                     //nest+="true;";
                     //System.out.println("!!-"+a2);
                     }
                     }
                     setCount++;
                     }*/
//                        }
                        /*if (a.getClassExpressionType().equals(ClassExpressionType.OBJECT_UNION_OF))
                     {
                     conjunct = a.asDisjunctSet();
                     for (OWLClassExpression b: conjunct)
                     {
                     System.out.println("-->"+b);
                     }
                     }*/

//                    }
                }

                //------------------
                //----ASSERTIONS----
                //------------------
                @Override
                public void visit(OWLClassAssertionAxiom axiom) {
                    count++;

                    if (!axiom.getClassExpression().isOWLThing()) {
                        String[] objects = new String[2];
                        objects[0] = getName(axiom.getIndividual() + "");
                        objects[1] = getName(axiom.getClassExpression() + "");
                        printSentence(objects, null, "ClassAssertion");
                    }
                }

                @Override
                public void visit(OWLObjectPropertyAssertionAxiom axiom) {
                    count++;
                    axiom = axiom.getSimplified();
                    String objects[] = {getName(axiom.getSubject() + ""), getName(axiom.getObject() + "")};
                    String roles[] = {getName(axiom.getProperty() + "")};
                    printSentence(objects, roles, "ObjectPropertyAssertion");
                }

                //-----------------------
                //---OBJECT PROPERTIES---
                //-----------------------
                @Override
                public void visit(OWLInverseObjectPropertiesAxiom axiom) {
                    count++;
                    String roles[] = {getName(axiom.getFirstProperty() + ""), getName(axiom.getSecondProperty() + "")};
                    printSentence(null, roles, "InverseObjectProperty");
                }

                @Override
                public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
                    count++;
                    printSentence(getName(axiom + ""), "TransitiveObjectProperty");
                }

                @Override
                public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
                    count++;
                    printSentence(getName(axiom + ""), "ReflexiveObjectProperty");
                }

                @Override
                public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
                    count++;
                    printSentence(getName(axiom + ""), "IrreflexiveObjectProperty");
                }

                @Override
                public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
                    count++;
                    String role = getName(axiom + "");
                    printFunctional(role);
                }

                @Override
                public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
                    count++;
                    printSentence(getName(axiom + ""), "SymmetricObjectProperty");
                }

                @Override
                public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
                    count++;
                    String role = getName(axiom + "");
                    role = role.replaceFirst("-", ";");
                    printSentence(null, role.split(";"), "AsymmetricObjectProperty");
                }

                //---------------------
                //---DATA PROPERTIES---
                //---------------------
                @Override
                public void visit(OWLFunctionalDataPropertyAxiom axiom) {
                    count++;
                    String role = getName(axiom + "");
                    printFunctional(role);
                }

                //----------------
                //----DISJOINT----
                //----------------
                @Override
                public void visit(OWLDisjointClassesAxiom axiom) {
                    count++;
                    disjointCount++;
                    Set<OWLDisjointClassesAxiom> classes = axiom.asPairwiseAxioms();
                    Set<OWLClassExpression> literals;
                    String[] objects = new String[2];
                    int i = 0;
                    for (OWLDisjointClassesAxiom c : classes) {
                        i = 0;
                        literals = c.getNestedClassExpressions();
                        for (OWLClassExpression l : literals) {
                            objects[i] = getName(l + "");
                            i++;
                        }
                        System.out.print("Disjoint ");

                        printSentence(objects, null, "Disjoint");
                    }
                }

                @Override
                public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
                    count++;
                    disjointCount++;
                    Set<OWLDisjointObjectPropertiesAxiom> classes = axiom.asPairwiseAxioms();
                    Set<OWLClassExpression> literals;
                    String[] objects = new String[2];
                    int i = 0;
                    for (OWLDisjointObjectPropertiesAxiom c : classes) {
                        i = 0;
                        literals = c.getNestedClassExpressions();
                        for (OWLClassExpression l : literals) {
                            objects[i] = getName(l + "");
                            i++;
                        }
                        System.out.print("Disjoint ");

                        printSentence(objects, null, "Disjoint");
                    }
                }

                @Override
                public void visit(OWLDisjointDataPropertiesAxiom axiom) {
                    count++;
                    disjointCount++;
                    Set<OWLDisjointDataPropertiesAxiom> classes = axiom.asPairwiseAxioms();
                    Set<OWLClassExpression> literals;
                    String[] objects = new String[2];
                    int i = 0;
                    for (OWLDisjointDataPropertiesAxiom c : classes) {
                        i = 0;
                        literals = c.getNestedClassExpressions();
                        for (OWLClassExpression l : literals) {
                            objects[i] = getName(l + "");
                            i++;
                        }
                        System.out.print("Disjoint ");

                        printSentence(objects, null, "Disjoint");
                    }
                }

                @Override
                public void visit(OWLDisjointUnionAxiom axiom) {
                    count++;
                    Set<OWLClassExpression> objects = axiom.getClassExpressions();
                    String[] literals = new String[objects.size() + 1];
                    literals[0] = getName(axiom.getOWLClass() + "");
                    int i = 1;
                    for (OWLClassExpression object : objects) {
                        literals[i] = getName(object + "");
                        i++;
                    }
                    printSentence(literals, null, "DisjointUnion");
                }

                //--------------
                //---SUBCLASS---
                //--------------
                @Override
                public void visit(OWLSubClassOfAxiom sub) {
                    String subClass = sub.getSubClass().toString();
                    OWLClassExpression superClassExpr = sub.getSuperClass();
                    String superClass = superClassExpr.toString();
                    if (superClassExpr.isClassExpressionLiteral()) {//CHECK FOR COMPLEMENTS!!
                        if (!(superClassExpr.isOWLThing())) {
                            String[] objects = {
                                getName(subClass),
                                getName(superClass)
                            };
                            System.out.print("Subclass ");
                            count++;
                            subClassCount++;
                            printSentence(objects, null, "OWLSubClassOfAxiom");
                        } else { //Not printing OWLThing
                            owlThingCount++;
                        }
                    } else {
                        count++;
                        subClassCount++;
                        String printString = getPartSentence(getName(subClass + "").split(";"), null, "PartObject", null);
                        printString += getClassExpression(superClassExpr.getNNF());
                        printFullSentence(printString);
                    }
                    /*else if (superClassExpr.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM) {
                     relationsDL(superClassExpr, subClass + "", "OWLObjectSomeValuesFrom");
                     } else if (superClassExpr.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM) {
                     relationsDL(superClassExpr, subClass + "", "OWLObjectAllValuesFrom");
                     //System.out.println(sub.getNNF());
                     } else if (superClassExpr.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
                     relationsDL(superClassExpr, subClass + "", "OWLObjectIntersectionOf");
                     }*/
                }

            };

            walker.walkStructure(visitor);

            //TESTING
            System.out.println("Number of axioms printed: " + count);
            System.out.println("Number subclass: " + subClassCount);
            System.out.println("Number disjoint: " + disjointCount);

            int numAxioms = o.getAxiomCount() - o.getAxiomCount(AxiomType.ANNOTATION_ASSERTION) - o.getAxiomCount(AxiomType.DECLARATION) - owlThingCount;
            System.out.println("Number of axioms: " + numAxioms); //TEST

            Set<OWLAxiom> a = o.getAxioms();
            for (OWLAxiom ax : a) {
                AxiomType type = ax.getAxiomType();

                /*if (!(type.getName().equals("SubClassOf")) && !(type.getName().equals("DisjointClasses")) && !(type.equals(AxiomType.ANNOTATION_ASSERTION)) && !(type.equals(AxiomType.DECLARATION)) && !(type.equals(AxiomType.CLASS_ASSERTION)) && !(type.equals(AxiomType.FUNCTIONAL_DATA_PROPERTY)) && !(type.equals(AxiomType.FUNCTIONAL_OBJECT_PROPERTY)) && !(type.equals(AxiomType.OBJECT_PROPERTY_ASSERTION))) {
                 System.out.println("!!!" + ax.toString());
                 }*/
            }

            System.out.println("Number of subclass: " + (o.getAxiomCount(AxiomType.SUBCLASS_OF) - owlThingCount)); //TEST
            System.out.println("Number of disjoint: " + o.getAxiomCount(AxiomType.DISJOINT_CLASSES)); //TEST
        } catch (OWLOntologyCreationException e) {
            System.out.println("EXCEPTION CAUGHT " + e);
        }
    }

    public static void printFunctional(String role) {
        role = role.replaceFirst("-", ";");
        String roles[] = role.split(";");
        if (roles[0].equals("het")) {
            roles[0] = "h" + (char) 234;
        }
        if (roles.length == 1) {
            String newRoles[] = {roles[0], "objek"};
            roles = newRoles;
        }

        printSentence(null, roles, "FunctionalProperty");
    }

    public static void nestRecursion(OWLClassExpression a) {
        int setCount = 1;
        Set<OWLClassExpression> conjunct = a.asConjunctSet();
        if (conjunct.size() == 1) {
            System.out.println("-_____" + conjunct);
            conjunct = a.asDisjunctSet();
            System.out.println("_______" + conjunct);
        }

        for (OWLClassExpression b : conjunct) {

            System.out.println("-->" + b);
            Set<OWLClassExpression> s2 = b.getNestedClassExpressions();
            if (s2.size() == 2) {
                ClassExpressionType type = b.getClassExpressionType();
                if (setCount < conjunct.size()) {
                    globalAndOr += "en;";
                }

                switch (type) {
                    case OBJECT_SOME_VALUES_FROM:
                        globalRoles += getName(b.getObjectPropertiesInSignature() + "") + ";";
                        globalLiterals += getName(b.getClassesInSignature() + "") + ";";

                        System.out.println(getName(b.getObjectPropertiesInSignature() + ""));
                        System.out.println(getName(b.getClassesInSignature() + ""));
                        globalNest += "false;";
                        break;
                    case OBJECT_ALL_VALUES_FROM:
                        break;

                }
            } else if (s2.size() > 2) {
                for (OWLClassExpression a2 : s2) {
                    ClassExpressionType type = a2.getClassExpressionType();

                    System.out.println("++++--" + a2);
                    System.out.println(b.getObjectPropertiesInSignature() + "");
                    switch (type) {
                        case OBJECT_INTERSECTION_OF:
                            break;
                        case OBJECT_UNION_OF:
                            globalRoles += "VREET;";
                            globalNest += "true;";
                            globalAndOr += "of;";
                            Set<OWLObjectProperty> set1 = b.getObjectPropertiesInSignature();
                            Set<OWLObjectProperty> set2 = a2.getObjectPropertiesInSignature();
                            for (OWLObjectProperty o : set2) {
                                set1.remove(o);
                            }
                            System.out.println(set1);
                            nestRecursion(a2);
                            break;
                    }
                    //nestRecursion(a2, roles, literals, andOr, nest);
                }
            }
            setCount++;
        }

    }

    public static void relationsDL(OWLClassExpression superClassExpr, String subClass, String type) {
        Set<OWLObjectProperty> objProp;
        Set<OWLClassExpression> nested = superClassExpr.getNestedClassExpressions();
        boolean negation = false;
        boolean union = false;
        boolean intersection = false;
        String literals = getName(subClass) + ";";
        String roles = "";
        for (OWLClassExpression c : nested) {
            c = c.getNNF();
            ClassExpressionType cet = c.getClassExpressionType();
            switch (cet) {
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
                    if (c.isClassExpressionLiteral()) {
                        literals += getName(c + "") + ";";
                    } else {
                        objProp = c.getObjectPropertiesInSignature();
                        for (OWLObjectProperty o : objProp) {
                            roles += getName(o + "") + ";";
                        }
                    }
                    break;
            }
        }
        if (type.equals("OWLObjectAllValuesFrom")) {
            roles = roles.replaceFirst("-", ";");
        }
        if (type.equals("OWLObjectIntersectionOf")) {
            type = "OWLObjectSomeValuesFrom";
        }
        //if (intersection && all roles are the same)
        System.out.print(type + " ");
        count++;
        subClassCount++;
        printSentence(literals.split(";"), roles.split(";"), type, negation, union, intersection);
    }

    public static Set<OWLObjectProperty> getTopLevelObjectProperty(OWLClassExpression ce) {
        Set<OWLObjectProperty> set1 = ce.getObjectPropertiesInSignature();
        Set<OWLClassExpression> nestedCEs = ce.getNestedClassExpressions();
        ClassExpressionType type = null;
        Set<OWLObjectProperty> set2 = null;
        for (OWLClassExpression nestedCE : nestedCEs) {
            type = nestedCE.getClassExpressionType();
            if (type == ClassExpressionType.OBJECT_UNION_OF
                    || type == ClassExpressionType.OBJECT_INTERSECTION_OF) {
                set2 = nestedCE.getObjectPropertiesInSignature();
                for (OWLObjectProperty o : set2) {
                    set1.remove(o);
                }
            }
        }
        return set1;
    }

    public static OWLClassExpression[] getNextClassExpression(OWLClassExpression ce) {
        Set<OWLClassExpression> nested = ce.getNestedClassExpressions();
        int size1 = nested.size();
        int maxSize = 0;
        OWLClassExpression nextCE = null;
        int size2;
        for (OWLClassExpression nestedCE : nested) {
            size2 = nestedCE.getNestedClassExpressions().size();
            if (size2 < size1 && size2 > maxSize) {
                maxSize = size2;
                nextCE = nestedCE;
            }
        }
        OWLClassExpression ceArray[] = {nextCE};
        return ceArray;
    }

    public static String getClassExpression(OWLClassExpression ce) {
        return getClassExpression(ce, "");
    }

    public static String getClassExpression(OWLClassExpression ce, String prevType) {
        String printSentence = "";
        OWLCardinalityRestriction cr;
        String roles;
        switch (ce.getClassExpressionType()) {
            case OWL_CLASS:
                if (ce.isOWLThing()) {
                    printSentence = "ding ";
                } else {
                    printSentence = getName(ce + "") + " ";
                }
                break;
            case OBJECT_SOME_VALUES_FROM:
                switch (prevType) {
                    case "PartObjectSomeValuesFrom":
                        printSentence = getPartSentence(null, null, "SomeReferringExpression", null);
                        break;
                    case "PartObjectAllValuesFrom":
                        printSentence = getPartSentence(null, null, "AllReferringExpression", null);
                        break;
                }
                printSentence += getPartSentence(null, getName(getTopLevelObjectProperty(ce) + "").split(";"), "PartObjectSomeValuesFrom", getNextClassExpression(ce), "PartObjectSomeValuesFrom");
                break;
            case OBJECT_ALL_VALUES_FROM:
                switch (prevType) {
                    case "PartObjectSomeValuesFrom":
                        printSentence = getPartSentence(null, null, "SomeReferringExpression", null);
                        break;
                    case "PartObjectAllValuesFrom":
                        printSentence = getPartSentence(null, null, "AllReferringExpression", null);
                        break;
                }
                roles = getName(getTopLevelObjectProperty(ce) + "");
                roles = roles.replaceFirst("-", ";");
                printSentence += getPartSentence(null, roles.split(";"), "PartObjectAllValuesFrom", getNextClassExpression(ce), "PartObjectAllValuesFrom");
                break;
            case OBJECT_MIN_CARDINALITY:
                cr = (OWLCardinalityRestriction) ce;
                printSentence = getPartSentence(cr.getCardinality(), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectMinCardinality", getNextClassExpression(ce));
                break;
            case OBJECT_MAX_CARDINALITY:
                cr = (OWLCardinalityRestriction) ce;
                printSentence = getPartSentence(cr.getCardinality(), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectMaxCardinality", getNextClassExpression(ce));
                break;
            case OBJECT_EXACT_CARDINALITY:
                cr = (OWLCardinalityRestriction) ce;
                printSentence = getPartSentence(cr.getCardinality(), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectExactCardinality", getNextClassExpression(ce));
                break;
            case OBJECT_HAS_VALUE:
                printSentence = getPartSentence(null, getName(getTopLevelObjectProperty(ce) + "").split(";"), "PartObjectHasValue", getNextClassExpression(ce));
                break;
            case OBJECT_HAS_SELF:
                printSentence = getPartSentence(null, getName(getTopLevelObjectProperty(ce) + "").split(";"), "PartObjectHasSelf", null);
                break;
            case DATA_SOME_VALUES_FROM:
                switch (prevType) {
                    case "PartObjectSomeValuesFrom":
                        printSentence = getPartSentence(null, null, "SomeReferringExpression", null);
                        break;
                    case "PartObjectAllValuesFrom":
                        printSentence = getPartSentence(null, null, "AllReferringExpression", null);
                        break;
                }
                printSentence += getPartSentence(null, getName(getTopLevelObjectProperty(ce) + "").split(";"), "PartObjectSomeValuesFrom", getNextClassExpression(ce), "PartObjectSomeValuesFrom");
                break;
            case DATA_ALL_VALUES_FROM:
                switch (prevType) {
                    case "PartObjectSomeValuesFrom":
                        printSentence = getPartSentence(null, null, "SomeReferringExpression", null);
                        break;
                    case "PartObjectAllValuesFrom":
                        printSentence = getPartSentence(null, null, "AllReferringExpression", null);
                        break;
                }
                roles = getName(getTopLevelObjectProperty(ce) + "");
                roles = roles.replaceFirst("-", ";");
                printSentence += getPartSentence(null, roles.split(";"), "PartObjectAllValuesFrom", getNextClassExpression(ce), "PartObjectAllValuesFrom");
                break;
            case DATA_MIN_CARDINALITY:
                cr = (OWLCardinalityRestriction) ce;
                printSentence = getPartSentence(cr.getCardinality(), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectMinCardinality", getNextClassExpression(ce));
                break;
            case DATA_MAX_CARDINALITY:
                cr = (OWLCardinalityRestriction) ce;
                printSentence = getPartSentence(cr.getCardinality(), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectMaxCardinality", getNextClassExpression(ce));
                break;
            case DATA_EXACT_CARDINALITY:
                cr = (OWLCardinalityRestriction) ce;
                printSentence = getPartSentence(cr.getCardinality(), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectExactCardinality", getNextClassExpression(ce));
                break;
            case DATA_HAS_VALUE:
                printSentence = getPartSentence(null, getName(getTopLevelObjectProperty(ce) + "").split(";"), "PartObjectHasValue", getNextClassExpression(ce));
                break;
            case OBJECT_INTERSECTION_OF:
                Set<OWLClassExpression> expressions = ce.asConjunctSet();
                OWLClassExpression[] ceArray = expressions.toArray(new OWLClassExpression[0]);
                printSentence = getPartSentence(null, null, "PartObjectIntersectionOf", ceArray, prevType);
                break;
            case OBJECT_UNION_OF:
                Set<OWLClassExpression> disjuncts = ce.asDisjunctSet();
                printSentence = getPartSentence(null, null, "PartObjectUnionOf", disjuncts.toArray(new OWLClassExpression[0]), prevType);
                break;
            case OBJECT_COMPLEMENT_OF:
                String objects[] = {getName(ce.getClassesInSignature() + "")};
                printSentence = getPartSentence(objects, null, "PartObjectComplementOf", null);
                break;
            case OBJECT_ONE_OF:
                Set<OWLNamedIndividual> tempSet = ce.getIndividualsInSignature();
                String[] objects2 = new String[tempSet.size()];
                int i = 0;
                for (OWLNamedIndividual c : tempSet) {
                    objects2[i] = getName(c + "");
                    i++;
                }
                printSentence = getPartSentence(objects2, null, "PartObjectOneOf", null);
                break;
            default:
                throw new AssertionError(ce.getClassExpressionType().name());
        }
        return printSentence;
    }

    public static int checkIfInt(String strIndex, int index) {
        if (!Character.isDigit(strIndex.charAt(0))) {
            strIndex = strIndex.replace("n", index + "");
            char ch;
            int num = Integer.parseInt(strIndex.charAt(0) + "");
            for (int i = 1; i < strIndex.length(); i++) {
                ch = strIndex.charAt(i);
                if (ch == '-') {
                    i++;
                    ch = strIndex.charAt(i);
                    num -= Integer.parseInt(ch + "");
                } else if (ch == '+') {
                    i++;
                    ch = strIndex.charAt(i);
                    num += Integer.parseInt(ch + "");
                }
            }
            return num;
        } else {
            return Integer.parseInt(strIndex);
        }
    }

    public static String iterateNodes(String printString, NodeList children, int index, String[] objects, String[] roles, OWLClassExpression[] ce) {
        return iterateNodes(printString, children, index, objects, roles, ce, "");
    }

    public static String iterateNodes(String printString, NodeList children, int index, String[] objects, String[] roles, OWLClassExpression[] ce, String prevType) {
        int thisIndex;
        Node child;
        if (null != children) {
            for (int i = 0; i < children.getLength(); i++) {
                child = children.item(i);
                switch (child.getNodeName()) {
                    case "Text":
                        printString += (child.getTextContent()) + " ";
                        break;
                    case "Object":
                        thisIndex = checkIfInt(child.getAttributes().getNamedItem("index").getTextContent(), index);
                        if (thisIndex < objects.length) {
                            printString += (objects[thisIndex]) + " ";
                        }
                        break;
                    case "Role":
                        thisIndex = checkIfInt(child.getAttributes().getNamedItem("index").getTextContent(), index);
                        if (thisIndex < roles.length
                                && (thisIndex == 0 || (thisIndex > 0 && !(roles[thisIndex].equals(roles[thisIndex - 1]))))) {
                            printString += (roles[thisIndex] + " ");
                        }
                        break;
                    case "Loop":
                        thisIndex = checkIfInt(child.getAttributes().getNamedItem("index").getTextContent(), index);
                        NodeList loopChildren = child.getChildNodes();
                        if (objects != null) {
                            while (thisIndex < objects.length) {
                                printString = iterateNodes(printString, loopChildren, thisIndex, objects, roles, ce);
                                thisIndex++;
                            }
                        } else if (ce != null) {
                            while (thisIndex < ce.length) {
                                printString = iterateNodes(printString, loopChildren, thisIndex, objects, roles, ce);
                                thisIndex++;
                            }
                        } else {
                            System.out.println("LOGIC ERROR IN LOOP");
                        }
                        break;
                    case "Cardinality":
                        printString += objects[0] + " ";
                        break;
                    case "ClassExpression":
                        thisIndex = checkIfInt(child.getAttributes().getNamedItem("index").getTextContent(), index);
                        if (thisIndex < ce.length) {
                            printString += getClassExpression(ce[thisIndex], prevType);
                        }
                        break;
                }
            }
        }
        return printString;
    }

    public static String getPartSentence(int cardinality, String[] roles, String type, OWLClassExpression[] ce) {
        String objects[] = {cardinality + ""};
        return getPartSentence(objects, roles, type, ce);
    }

    public static String getPartSentence(String[] objects, String[] roles, String type, OWLClassExpression[] ce) {
        return getPartSentence(objects, roles, type, ce, "");
    }

    public static String getPartSentence(String[] objects, String[] roles, String type, OWLClassExpression[] ce, String prevType) {
        Node prop = null;
        String cType = "";
        for (int j = 0; j < constraints.getLength(); j++) {
            cType = constraints.item(j).getAttributes().getNamedItem("type").toString();
            if (cType.equals("type=\"" + type + "\"")) {
                prop = constraints.item(j);
                break;
            }
        }
        NodeList children = prop.getChildNodes();
        return iterateNodes("", children, 0, objects, roles, ce, prevType);
    }

    public static void printFullSentence(String printString) {
        printString = printString.trim() + ".";
        printString = printString.replace("-", " ");
        printString = printString.replace("? ", "");
        printString = printString.replace(" ?", "");
        System.out.println(printString);
    }

    public static void printSentence(String[] objects, String[] roles, String type, boolean negation, boolean union, boolean intersection) {
        printSentence(objects, roles, null, type, negation, union, intersection);
    }

    public static void printSentence(String[] objects, String[] roles, String type) {
        printSentence(objects, roles, null, type, false, false, false);
    }

    public static void printSentence(String role, String type) {
        String[] roles = new String[1];
        roles[0] = role;
        printSentence(null, roles, null, type, false, false, false);
    }

    public static void printSentence(String[] objects, String[] roles, String[] nest, String type, boolean negation, boolean union, boolean intersection) {
        //Choose constraint based on type
        //FIND MORE GENERIC WAY TO DO THIS??
        String printString = "";
        Node prop = null;
        String cType = "";
        for (int j = 0; j < constraints.getLength(); j++) {
            cType = constraints.item(j).getAttributes().getNamedItem("type").toString();
            if (!negation && !union && !intersection && cType.equals("type=\"" + type + "\"")
                    || (negation && cType.equals("type=\"" + type + " negation\""))
                    || (union && cType.equals("type=\"" + type + " union\""))
                    || (intersection && cType.equals("type=\"" + type + " intersection\""))) {
                prop = constraints.item(j);
                break;
            }
        }
        NodeList children = prop.getChildNodes();
        printString = iterateNodes(printString, children, 0, objects, roles, null);
        /*Node child;
         if (null != children) {
         for (int i = 0; i < children.getLength(); i++) {
         child = children.item(i);
         switch (child.getNodeName()) {
         case "Text":
         printString += (child.getTextContent());
         break;
         case "Object":
         index = Integer.parseInt(child.getAttributes().getNamedItem("index").getTextContent());
         printString += (objects[index]);
         break;
         case "Role":
         index = Integer.parseInt(child.getAttributes().getNamedItem("index").getTextContent());
         if (index < roles.length) {
         printString += (roles[index] + " ");
         }
         break;
         case "Loop":
         //make separate method
         index = Integer.parseInt(child.getAttributes().getNamedItem("index").getTextContent());
         NodeList loopChildren = child.getChildNodes();
         Node loopChild;
         while (index < objects.length) {
         for (int j = 0; j < loopChildren.getLength(); j++) {
         loopChild = loopChildren.item(j);
         switch (loopChild.getNodeName()) {
         case "Text":
         printString += (loopChild.getTextContent());
         break;
         case "Object":
         printString += (objects[index]);
         break;
         case "Role":
         if (index > 0 && !(roles[index - 1].equals(roles[index - 2]))) {
         printString += (roles[index - 1] + " ");
         }
         break;
         case "Nest"://Rename loop?
         if (nest[index-1].equals("true"))
         {
         //look at children of Nest
         }
         break;
         case "Else":
         if (nest[index-1].equals("false"))
         {
         //print object
         }
         break;
         case "AndOr":
         //printString+=(andOr[index-1]+" ");
         break;
         }
         }
         index++;
         }
         }
         }
         }*/
        printString = printString.trim() + ".";
        printString = printString.replace("-", " ");
        printString = printString.replace("? ", "");
        printString = printString.replace(" ?", "");
        System.out.println(printString);
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

    private static String getName(String literal) {
        return literal.substring(literal.indexOf("#") + 1, literal.indexOf(">"));
    }

}
