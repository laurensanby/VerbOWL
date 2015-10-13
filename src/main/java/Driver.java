
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collections;
import java.util.List;
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

    static int count, subClassCount, subClassSentCount, disjointCount, owlThingCount, sentenceCount, equivalentCount, equivalentSentCount, disjointSentCount, subPropertyCount, subPropertySentCount, assertionCount, assertionSentCount;
    static int inverseCount, transitiveCount, reflexiveCount, irreflexiveCount, functionalCount, inverseFunctionalCount, symmetricCount, asymmetricCount, domainCount, rangeCount;
    static int inverseSentCount, transitiveSentCount, reflexiveSentCount, irreflexiveSentCount, functionalSentCount, inverseSentFunctionalCount, symmetricSentCount, asymmetricSentCount, domainSentCount, rangeSentCount;
    static String globalRoles, globalLiterals, globalAndOr, globalNest;
    static NodeList constraints;
    static final String fileName = "stuff.owl";

    public static void main(String[] args) throws IOException {
        // TODO code application logic here
        count = 0;
        sentenceCount = 0;
        equivalentCount = equivalentSentCount = 0;
        subClassCount = subClassSentCount = 0;
        disjointCount = disjointSentCount = 0;
        owlThingCount = 0;
        subPropertyCount = subPropertySentCount = 0;
        assertionCount = assertionSentCount = 0;
        inverseCount = transitiveCount = reflexiveCount = irreflexiveCount = functionalCount = inverseFunctionalCount = symmetricCount = asymmetricCount = domainCount = rangeCount = 0;
        inverseSentCount = transitiveSentCount = reflexiveSentCount = irreflexiveSentCount = functionalSentCount = inverseSentFunctionalCount = symmetricSentCount = asymmetricSentCount = domainSentCount = rangeSentCount = 0;
        long startTime = System.nanoTime();

        try {
            File f = new File("C:\\Users\\Lauren\\Documents\\UCT\\Honours\\project\\Ontologies\\" + fileName);
            OWLOntologyManager m = OWLManager.createOWLOntologyManager();
            OWLOntology o = m.loadOntologyFromOntologyDocument(f);
            constraints = readXML("template_v1.xml");

            File outputF = new File("output-" + fileName.substring(0, fileName.indexOf(".")) + ".txt");

            // if file doesnt exists, then create it
            if (!outputF.exists()) {
                outputF.createNewFile();
            }
            //ensure file starts empty
            BufferedWriter bw = new BufferedWriter(new FileWriter(outputF));
            bw.write("");
            bw.close();

            //walker
            OWLOntologyWalker walker = new OWLOntologyWalker(Collections.singleton(o));
            OWLOntologyWalkerVisitor visitor;
            visitor = new OWLOntologyWalkerVisitor(walker) {

                //------------------------
                //---EQUIVALENT CLASSES---
                //------------------------
                @Override
                public void visit(OWLEquivalentClassesAxiom axiom) {
                    String printString = "EquivalentClass " + getPartSentence(getName(axiom.getNamedClasses() + "").split(";"), null, "PartObject", null);
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
                    equivalentCount++;
                    printString += getClassExpression(ce.getNNF());
                    printFullSentence(printString);
                }

                //------------------
                //----ASSERTIONS----
                //------------------
                //Same Individuals
                @Override
                public void visit(OWLSameIndividualAxiom axiom) {

                    Set<OWLIndividual> ind = axiom.getIndividuals();
                    String objects = "";
                    for (OWLIndividual i : ind) {
                        objects += getName(i + "") + ";";
                    }
                    count++;
                    assertionCount++;
                    printSentence(objects.split(";"), null, "SameIndividual");
                }

                //Different Individuals
                @Override
                public void visit(OWLDifferentIndividualsAxiom axiom) {
                    count++;
                    assertionCount++;
                    Set<OWLIndividual> ind = axiom.getIndividuals();
                    String objects = "";
                    for (OWLIndividual i : ind) {
                        objects += getName(i + "") + ";";
                    }
                    printSentence(objects.split(";"), null, "DifferentIndividual");
                }

                @Override
                public void visit(OWLClassAssertionAxiom axiom) {
                    if (!axiom.getClassExpression().isOWLThing()) {
                        count++;
                        assertionCount++;
                        String[] objects = new String[2];
                        objects[0] = getName(axiom.getIndividual() + "");
                        objects[1] = getName(axiom.getClassExpression() + "");
                        printSentence(objects, null, "ClassAssertion");
                    } else {
                        owlThingCount++;
                    }
                }

                @Override
                public void visit(OWLObjectPropertyAssertionAxiom axiom) {
                    count++;
                    assertionCount++;
                    axiom = axiom.getSimplified();
                    String objects[] = {getName(axiom.getSubject() + ""), getName(axiom.getObject() + "")};
                    String roles[] = {getName(axiom.getProperty() + "")};
                    printSentence(objects, roles, "ObjectPropertyAssertion");
                }

                //DataPropertyAssertion
                @Override
                public void visit(OWLDataPropertyAssertionAxiom axiom) {
                    count++;
                    assertionCount++;
                    String objects[] = {getName(axiom.getSubject() + ""), getLiteralName(axiom.getObject() + "")};
                    String roles[] = {getName(axiom.getProperty() + "")};
                    printSentence(objects, roles, "DataPropertyAssertion");
                }

                //NegativeObjectPropertyAssertion
                @Override
                public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {
                    count++;
                    assertionCount++;
                    String objects[] = {getName(axiom.getSubject() + ""), getName(axiom.getObject() + "")};
                    String roles = getName(axiom.getProperty() + "");
                    roles = roles.replace("-", ";");
                    printSentence(objects, roles.split(";"), "NegativeObjectPropertyAssertion");
                }

                //NegativeDataPropertyAssertion
                @Override
                public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {
                    count++;
                    assertionCount++;
                    String objects[] = {getName(axiom.getSubject() + ""), getLiteralName(axiom.getObject() + "")};
                    String roles[] = {getName(axiom.getProperty() + "")};
                    printSentence(objects, roles, "NegativeDataPropertyAssertion");
                }

                //-----------------------
                //---OBJECT PROPERTIES---
                //-----------------------
                @Override
                public void visit(OWLInverseObjectPropertiesAxiom axiom) {
                    count++;
                    inverseCount++;
                    String roles[] = {getName(axiom.getFirstProperty() + ""), getName(axiom.getSecondProperty() + "")};
                    printSentence(null, roles, "InverseObjectProperty");
                }

                @Override
                public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
                    count++;
                    transitiveCount++;
                    printSentence(getName(axiom + ""), "TransitiveObjectProperty");
                }

                @Override
                public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
                    count++;
                    reflexiveCount++;
                    printSentence(getName(axiom + ""), "ReflexiveObjectProperty");
                }

                @Override
                public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
                    count++;
                    irreflexiveCount++;
                    printSentence(getName(axiom + ""), "IrreflexiveObjectProperty");
                }

                @Override
                public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
                    count++;
                    functionalCount++;
                    String role = getName(axiom + "");
                    printFunctional(role);
                }

                @Override
                public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
                    count++;
                    inverseFunctionalCount++;
                    printSentence(getName(axiom + ""), "InverseFunctionalObjectProperty");
                }

                @Override
                public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
                    count++;
                    symmetricCount++;
                    printSentence(getName(axiom + ""), "SymmetricObjectProperty");
                }

                @Override
                public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
                    count++;
                    asymmetricCount++;
                    String role = getName(axiom + "");
                    role = role.replaceFirst("-", ";");
                    printSentence(null, role.split(";"), "AsymmetricObjectProperty");
                }

                @Override
                public void visit(OWLSubObjectPropertyOfAxiom axiom) {
                    String role = getName(axiom.getSubProperty() + "") + ";";
                    OWLObjectPropertyExpression ope = axiom.getSuperProperty();
                    if (!ope.isOWLTopObjectProperty()) {
                        count++;
                        subPropertyCount++;
                        role += getName(ope + "");
                        printSentence(null, role.split(";"), "SubObjectProperty");
                    } else {
                        owlThingCount++;
                    }
                }

                @Override
                public void visit(OWLSubPropertyChainOfAxiom axiom) {
                    count++;
                    subPropertyCount++;
                    String role = getName(axiom.getSuperProperty() + "") + ";";
                    List<OWLObjectPropertyExpression> ope = axiom.getPropertyChain();
                    for (OWLObjectPropertyExpression ope1 : ope) {
                        role += getName(ope1 + "") + ";";
                    }
                    role = role.substring(0, role.length() - 1);
                    printSentence(null, role.split(";"), "SubObjectProperty");
                }

                @Override
                public void visit(OWLObjectPropertyDomainAxiom axiom) {
                    if (!axiom.getDomain().isOWLThing()) {
                        count++;
                        domainCount++;
                        OWLClassExpression ce[] = {axiom.getDomain()};
                        String printString = "ObjectPropertyDomain " + getPartSentence(null, getName(axiom.getObjectPropertiesInSignature() + "").split(";"), "ObjectPropertyDomain", ce, "ObjectPropertyDomain");
                        printFullSentence(printString);
                    } else {
                        owlThingCount++;
                    }
                }

                @Override
                public void visit(OWLObjectPropertyRangeAxiom axiom) {
                    if (!axiom.getRange().isOWLThing()) {
                        count++;
                        rangeCount++;
                        OWLClassExpression ce[] = {axiom.getRange()};
                        String roles = getName(axiom.getObjectPropertiesInSignature() + "");
                        roles = roles.replaceFirst("-", ";");
                        String printString = "ObjectPropertyRange " + getPartSentence(null, roles.split(";"), "ObjectPropertyRange", ce, "ObjectPropertyRange");
                        printFullSentence(printString);
                    } else {
                        owlThingCount++;
                    }
                }

                //---------------------
                //---DATA PROPERTIES---
                //---------------------
                @Override
                public void visit(OWLSubDataPropertyOfAxiom axiom) {
                    String role = getName(axiom.getSubProperty() + "") + ";";
                    OWLDataPropertyExpression ode = axiom.getSuperProperty();
                    if (!ode.isOWLTopDataProperty()) {
                        count++;
                        subPropertyCount++;
                        role += getName(ode + "");
                        printSentence(null, role.split(";"), "SubObjectProperty");
                    } else {
                        owlThingCount++;
                    }
                }

                @Override
                public void visit(OWLDataPropertyDomainAxiom axiom) {
                    if (!axiom.getDomain().isOWLThing()) {
                        count++;
                        domainCount++;
                        OWLClassExpression ce[] = {axiom.getDomain()};
                        String printString = "DataPropertyDomain " + getPartSentence(null, getName(axiom.getDataPropertiesInSignature() + "").split(";"), "DataPropertyDomain", ce, "ObjectPropertyDomain");
                        printFullSentence(printString);
                    } else {
                        owlThingCount++;
                    }
                }

                @Override
                public void visit(OWLDataPropertyRangeAxiom axiom) {
                    OWLDataRange dr = axiom.getRange();
                    if (!dr.isTopDatatype()) {
                        if (dr.isDatatype()) {
                            count++;
                            rangeCount++;
                            OWLDatatype dt = dr.asOWLDatatype();
                            String objects[] = {getDataName(dt.getIRI() + "")};
                            String roles[] = {getName(axiom.getDataPropertiesInSignature() + "")};
                            printSentence(objects, roles, "DataPropertyRange");
                        }
                    }
                }

                @Override
                public void visit(OWLFunctionalDataPropertyAxiom axiom) {
                    count++;
                    functionalCount++;
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

                        printSentence(objects, null, "Disjoint");
                    }
                }

                @Override
                public void visit(OWLDisjointUnionAxiom axiom) {
                    count++;
                    disjointCount++;
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
                            count++;
                            subClassCount++;
                            printSentence(objects, null, "OWLSubClassOfAxiom");
                        } else { //Not printing OWLThing
                            owlThingCount++;
                        }
                    } else {
                        count++;
                        subClassCount++;
                        String printString = "Complex SubClass " + getPartSentence(getName(subClass + "").split(";"), null, "PartObject", null);
                        printString += getClassExpression(superClassExpr.getNNF());
                        printFullSentence(printString);
                    }
                }

            };

            walker.walkStructure(visitor);

            //TESTING
            long duration = System.nanoTime() - startTime;
            double seconds = (double) duration / 1000000000.0;
            int numAxioms = o.getAxiomCount() - o.getAxiomCount(AxiomType.ANNOTATION_ASSERTION) - o.getAxiomCount(AxiomType.DECLARATION);
            int numDisjoint = o.getAxiomCount(AxiomType.DISJOINT_CLASSES) + o.getAxiomCount(AxiomType.DISJOINT_UNION) + o.getAxiomCount(AxiomType.DISJOINT_DATA_PROPERTIES) + o.getAxiomCount(AxiomType.DISJOINT_OBJECT_PROPERTIES);
            int numSubProperty = o.getAxiomCount(AxiomType.SUB_DATA_PROPERTY) + o.getAxiomCount(AxiomType.SUB_OBJECT_PROPERTY) + o.getAxiomCount(AxiomType.SUB_PROPERTY_CHAIN_OF);
            int numAssertions = o.getAxiomCount(AxiomType.CLASS_ASSERTION) + o.getAxiomCount(AxiomType.OBJECT_PROPERTY_ASSERTION) + o.getAxiomCount(AxiomType.DATA_PROPERTY_ASSERTION) + o.getAxiomCount(AxiomType.NEGATIVE_DATA_PROPERTY_ASSERTION) + o.getAxiomCount(AxiomType.NEGATIVE_OBJECT_PROPERTY_ASSERTION) + o.getAxiomCount(AxiomType.SAME_INDIVIDUAL) + o.getAxiomCount(AxiomType.DIFFERENT_INDIVIDUALS);
            int numFunctional = o.getAxiomCount(AxiomType.FUNCTIONAL_DATA_PROPERTY) + o.getAxiomCount(AxiomType.FUNCTIONAL_OBJECT_PROPERTY);
            int numDomain = o.getAxiomCount(AxiomType.OBJECT_PROPERTY_DOMAIN) + o.getAxiomCount(AxiomType.DATA_PROPERTY_DOMAIN);
            int numRange = o.getAxiomCount(AxiomType.OBJECT_PROPERTY_RANGE) + o.getAxiomCount(AxiomType.DATA_PROPERTY_RANGE);
            try {
                File testFile = new File(fileName.substring(0, fileName.indexOf(".")) + "TestData.csv");

                // if file doesnt exists, then create it
                if (!testFile.exists()) {
                    testFile.createNewFile();
                }
                bw = new BufferedWriter(new FileWriter(testFile));
                bw.write(fileName + ";Num axioms in ontology;Num axioms verbalised;Num sentences written\n");
                bw.write("Total;" + numAxioms + ";" + count + ";" + sentenceCount + "\n");
                bw.write("EquivalentClass;" + o.getAxiomCount(AxiomType.EQUIVALENT_CLASSES) + ";" + equivalentCount + ";" + equivalentSentCount + "\n");
                bw.write("SubClass;" + o.getAxiomCount(AxiomType.SUBCLASS_OF) + ";" + subClassCount + ";" + subClassSentCount + "\n");
                bw.write("Disjoint;" + numDisjoint + ";" + disjointCount + ";" + disjointSentCount + "\n");
                bw.write("SubProperty;" + numSubProperty + ";" + subPropertyCount + ";" + subPropertySentCount + "\n");
                bw.write("Inverse OP;" + o.getAxiomCount(AxiomType.INVERSE_OBJECT_PROPERTIES) + ";" + inverseCount + ";" + inverseSentCount + "\n");
                bw.write("Transitive OP;" + o.getAxiomCount(AxiomType.TRANSITIVE_OBJECT_PROPERTY) + ";" + transitiveCount + ";" + transitiveSentCount + "\n");
                bw.write("Reflexive OP;" + o.getAxiomCount(AxiomType.REFLEXIVE_OBJECT_PROPERTY) + ";" + reflexiveCount + ";" + reflexiveSentCount + "\n");
                bw.write("Irreflexive OP;" + o.getAxiomCount(AxiomType.IRREFLEXIVE_OBJECT_PROPERTY) + ";" + irreflexiveCount + ";" + irreflexiveSentCount + "\n");
                bw.write("Functional;" + numFunctional + ";" + functionalCount + ";" + functionalSentCount + "\n");
                bw.write("InverseFunctional OP;" + o.getAxiomCount(AxiomType.INVERSE_FUNCTIONAL_OBJECT_PROPERTY) + ";" + inverseFunctionalCount + ";" + inverseSentFunctionalCount + "\n");
                bw.write("Symmetric OP;" + o.getAxiomCount(AxiomType.SYMMETRIC_OBJECT_PROPERTY) + ";" + symmetricCount + ";" + symmetricSentCount + "\n");
                bw.write("Asymmetric OP;" + o.getAxiomCount(AxiomType.ASYMMETRIC_OBJECT_PROPERTY) + ";" + asymmetricCount + ";" + asymmetricSentCount + "\n");
                bw.write("Domain;" + numDomain + ";" + domainCount + ";" + domainSentCount + "\n");
                bw.write("Range;" + numRange + ";" + rangeCount + ";" + rangeSentCount + "\n");
                bw.write("Assertions;" + numAssertions + ";" + assertionCount + ";" + assertionSentCount + "\n");
                bw.write("\nOwlThing;" + owlThingCount + "\n");
                bw.write("Time taken;" + seconds);
                bw.close();
                //subClassCount, disjointCount, owlThingCount, sentenceCount, equivalentCount, sameIndividualCount
            } catch (IOException e) {
            }

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
        if (ce != null) {
            switch (ce.getClassExpressionType()) {
                case OWL_CLASS:
                    if (ce.isOWLThing()) {
                        printSentence = "tipe ";
                    } else {
                        if (prevType.equals("PartObjectSomeValuesFrom") || prevType.equals("PartObjectAllValuesFrom") || prevType.equals("ObjectPropertyDomain") || prevType.equals("ObjectPropertyRange") || prevType.contains("Cardinality")) {
                            printSentence = getName(ce + "") + " ";
                        } else {
                            printSentence = "is " + getName(ce + "") + " ";
                        }
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
                    OWLObjectPropertyExpression someProp = ((OWLObjectSomeValuesFrom) ce).getProperty();
                    String somePropStr = getName(someProp + "");
                    if (someProp.isAnonymous()) {
                        OWLObjectInverseOf inverse = (OWLObjectInverseOf) someProp;
                        String inverseStr = getName(inverse.getInverse() + "");
                        if ((inverseStr).equals(somePropStr)) {
                            somePropStr = "die inverse van " + somePropStr;
                        } else {
                            somePropStr = inverseStr;
                        }
                    }
                    printSentence += getPartSentence(null, somePropStr.split(";"), "PartObjectSomeValuesFrom", getNextClassExpression(ce), "PartObjectSomeValuesFrom");
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
                    OWLObjectPropertyExpression allProp = ((OWLObjectAllValuesFrom) ce).getProperty();
                    roles = getName(allProp + "");
                    if (allProp.isAnonymous()) {
                        OWLObjectInverseOf inverse = (OWLObjectInverseOf) allProp;
                        String inverseStr = getName(inverse.getInverse() + "");
                        if (inverseStr.equals(roles)) {
                            roles = "die inverse van " + roles;
                        } else {
                            roles = inverseStr;
                        }
                    }
                    roles = roles.replaceFirst("-", ";");
                    printSentence += getPartSentence(null, roles.split(";"), "PartObjectAllValuesFrom", getNextClassExpression(ce), "PartObjectAllValuesFrom");
                    break;
                case OBJECT_MIN_CARDINALITY:
                    cr = (OWLCardinalityRestriction) ce;
                    printSentence = getPartSentence((cr.getCardinality() + "").split(";"), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectMinCardinality", getNextClassExpression(ce), "Cardinality");
                    break;
                case OBJECT_MAX_CARDINALITY:
                    cr = (OWLCardinalityRestriction) ce;
                    printSentence = getPartSentence((cr.getCardinality() + "").split(";"), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectMaxCardinality", getNextClassExpression(ce), "Cardinality");
                    break;
                case OBJECT_EXACT_CARDINALITY:
                    cr = (OWLCardinalityRestriction) ce;
                    printSentence = getPartSentence((cr.getCardinality() + "").split(";"), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectExactCardinality", getNextClassExpression(ce), "Cardinality");
                    break;
                case OBJECT_HAS_VALUE:
                    printSentence = getPartSentence(null, (((OWLObjectHasValue) ce).getProperty() + "").split(";"), "PartObjectHasValue", getNextClassExpression(ce));
                    break;
                case OBJECT_HAS_SELF:
                    printSentence = getPartSentence(null, (((OWLObjectHasSelf) ce).getProperty() + "").split(";"), "PartObjectHasSelf", null);
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
                    String[] dataName = new String[1];
                    OWLClassExpression[] nextCE = getNextClassExpression(ce);
                    String role = getName(((OWLDataSomeValuesFrom) ce).getProperty() + "");
                    if (nextCE[0] == null) {
                        OWLDataSomeValuesFrom dsvf = (OWLDataSomeValuesFrom) ce;
                        OWLDatatypeRestriction dtr = null;
                        OWLDataRange dr = dsvf.getFiller();
                        try {
                            dtr = (OWLDatatypeRestriction) dr;
                        } catch (Exception e) {
                        }
                        if (dtr != null) {
                            Set<OWLFacetRestriction> facetsR = dtr.getFacetRestrictions();
                            for (OWLFacetRestriction facetR : facetsR) {
                                String facet = (facetR.getFacet() + "");
                                String fValue = facetR.getFacetValue().getLiteral();
                                switch (facet) {
                                    case "maxInclusive":
                                        printSentence += getPartSentence(fValue.split(";"), role.split(";"), "PartDataSomeValuesFromMax", null, "PartObjectSomeValuesFrom");
                                        break;
                                    case "minInclusive":
                                        printSentence += getPartSentence(fValue.split(";"), role.split(";"), "PartDataSomeValuesFromMin", null, "PartObjectSomeValuesFrom");
                                        break;
                                }
                                break;
                            }
                        } else {
                            dataName[0] = getName(dr + "");
                            printSentence += getPartSentence(dataName, role.split(";"), "PartDataSomeValuesFrom", null, "PartObjectSomeValuesFrom");
                        }
                    } else {
                        printSentence += getPartSentence(null, role.split(";"), "PartObjectSomeValuesFrom", nextCE, "PartObjectSomeValuesFrom");
                    }
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
                    roles = getName(((OWLDataAllValuesFrom) ce).getProperty() + "");
                    roles = roles.replaceFirst("-", ";");
                    printSentence += getPartSentence(null, roles.split(";"), "PartObjectAllValuesFrom", getNextClassExpression(ce), "PartObjectAllValuesFrom");
                    break;
                case DATA_MIN_CARDINALITY:
                    cr = (OWLCardinalityRestriction) ce;
                    printSentence = getPartSentence((cr.getCardinality() + "").split(";"), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectMinCardinality", getNextClassExpression(ce), "Cardinality");
                    break;
                case DATA_MAX_CARDINALITY:
                    cr = (OWLCardinalityRestriction) ce;
                    printSentence = getPartSentence((cr.getCardinality() + "").split(";"), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectMaxCardinality", getNextClassExpression(ce), "Cardinality");
                    break;
                case DATA_EXACT_CARDINALITY:
                    cr = (OWLCardinalityRestriction) ce;
                    printSentence = getPartSentence((cr.getCardinality() + "").split(";"), getName(ce.getObjectPropertiesInSignature() + "").split(";"), "PartObjectExactCardinality", getNextClassExpression(ce), "Cardinality");
                    break;
                case DATA_HAS_VALUE:
                    printSentence = getPartSentence(null, getName(((OWLDataHasValue) ce).getProperty() + "").split(";"), "PartObjectHasValue", getNextClassExpression(ce));
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
                    System.out.println("!!!" + ce.getClassExpressionType().name());
                    throw new AssertionError(ce.getClassExpressionType().name());
            }
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
                                printString = iterateNodes(printString, loopChildren, thisIndex, objects, roles, ce, prevType);
                                thisIndex++;
                            }
                        } else if (roles != null) {
                            while (thisIndex < roles.length) {
                                printString = iterateNodes(printString, loopChildren, thisIndex, objects, roles, ce);
                                thisIndex++;
                            }
                        } else {
                            System.out.println("LOGIC ERROR IN LOOP " + printString);
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

    public static void printSentence(String role, String type) {
        String[] roles = new String[1];
        roles[0] = role;
        printSentence(null, roles, type);
    }

    public static void printSentence(String[] objects, String[] roles, String type) {
        //Choose constraint based on type
        String printString = "";
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
        printString = type + " " + iterateNodes(printString, children, 0, objects, roles, null);
        printFullSentence(printString);
    }

    public static void printFullSentence(String printString) {
        printString = printString.trim() + ".";
        printString = printString.replace("-", " ");
        printString = printString.replace("? ", "");
        printString = printString.replace(" ?", "");
        //add writer to append to new line of file

        try {
            File outputF = new File("output-" + fileName.substring(0, fileName.indexOf(".")) + ".txt");

            BufferedWriter bw = new BufferedWriter(new FileWriter(outputF, true));
            bw.append(printString + "\n");
            sentenceCount++;
            if (printString.contains("EquivalentClass")) {
                equivalentSentCount++;
            } else if (printString.contains("Disjoint")) {
                disjointSentCount++;
            } else if (printString.contains("SubObjectProperty")) {
                subPropertySentCount++;
            } else if (printString.contains("Assertion") || (printString.contains("DifferentIndividual")) || (printString.contains("SameIndividual"))) {
                assertionSentCount++;
            } else if (printString.contains("SubClass")) {
                subClassSentCount++;
            } else if (printString.contains("InverseObjectProperty")) {
                inverseSentCount++;
            } else if (printString.contains("Transitive")) {
                transitiveSentCount++;
            } else if (printString.substring(0, 9).equals("Reflexive")) {
                reflexiveSentCount++;
            } else if (printString.contains("Irreflexive")) {
                irreflexiveSentCount++;
            } else if (printString.contains("FunctionalProperty")) {
                functionalSentCount++;
            } else if (printString.contains("InverseFunctionalObjectProperty")) {
                inverseSentFunctionalCount++;
            } else if (printString.substring(0, 9).equals("Symmetric")) {
                symmetricSentCount++;
            } else if (printString.contains("AsymmetricObjectProperty")) {
                assertionSentCount++;
            } else if (printString.contains("Domain")) {
                domainSentCount++;
            } else if (printString.contains("Range")) {
                rangeSentCount++;
            }
            bw.close();
        } catch (IOException e) {
            System.out.println(printString);
        }
        //System.out.println(printString);
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
        if (literal.contains("#") && literal.contains(">")) {
            return literal.substring(literal.indexOf("#") + 1, literal.indexOf(">"));
        } else {
            return literal;
        }
    }

    private static String getDataName(String literal) {
        if (literal.contains("#")) {
            return literal.substring(literal.indexOf("#") + 1);
        } else {
            return literal.substring(literal.indexOf(":") + 1);
        }
    }

    private static String getLiteralName(String literal) {
        literal = literal.substring(1);
        return literal.substring(0, literal.indexOf("\""));
    }
}
