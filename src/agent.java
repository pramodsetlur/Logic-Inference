import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

//Data structure for each predicate
class Predicate
{
	String completeQuery;
	String predicate;
	String argument1;
	String argument2;
	
	//separate the sentences into the predicate name, arguement1, arguement2
	Predicate(String sentence)
	{
		completeQuery = new String(sentence);
				
		int indexOfOpenBraces = sentence.indexOf('(');
		int indexOfcomma = sentence.indexOf(',');
		int indexOfCloseBraces = sentence.indexOf(')');
		
		this.predicate = new String(sentence.substring(0,indexOfOpenBraces));
		if(indexOfcomma < 0)
			this.argument1 = new String(sentence.substring(indexOfOpenBraces+1,indexOfCloseBraces));
		else
			this.argument1 = new String(sentence.substring(indexOfOpenBraces+1,indexOfcomma));
		
		if(indexOfcomma > 0)
			this.argument2 = new String(sentence.substring(indexOfcomma+1, sentence.length()-1));
		else 
			this.argument2 = null;
	}
	
	//Deep copy of a predicate
	Predicate(Predicate tempPredicate)
	{
		completeQuery = new String(tempPredicate.completeQuery);
		predicate = new String(tempPredicate.predicate);
		argument1 = new String(tempPredicate.argument1);
		if(tempPredicate.argument2 != null)
			argument2 = new String(tempPredicate.argument2);
	}
}

//Data structure for all the clauses given to the KB
class Implication
{
	//LHS of the predicate is an arraylist of predicates
	ArrayList<Predicate> lhs;
	Predicate rhs;
	
	Implication(ArrayList<Predicate> lhs, String conclusion)
	{
		this.rhs = new Predicate(conclusion);		
		this.lhs = new ArrayList<Predicate>(lhs);
	}
}

//Data structure for all the facts given to the KB
class Fact
{
	Predicate rhs;
	Fact(String sentence)
	{
		this.rhs = new Predicate(sentence);
	}
}



//Data structure for the entire knowledge base which contains the ask query and the known input data
class KnowledgeBase
{
	//The KB contains the clauses and the facts
	Predicate askQuery;
	ArrayList<Implication> allImplications;
	ArrayList<Fact> allFacts;
	ArrayList<Predicate> toCheckPredicateList = new ArrayList<Predicate>();
	ArrayList<Predicate> traversed = new ArrayList<Predicate>();
	
	public KnowledgeBase(String ask, ArrayList<String> sentences) 
	{
		this.askQuery = initializeAskQuery(this.askQuery, ask);
		this.allImplications = initializeImplications(sentences);
		this.allFacts = initializeFacts(sentences);
	}
	
	//initializing the 'ask' query and splitting the sentences into the predicateName, argument1, argument2
	Predicate initializeAskQuery(Predicate askQuery, String ask)
	{
		askQuery = new Predicate(ask);
		return askQuery;
	}
	
	//initializing the implications in the sentences
	ArrayList<Implication> initializeImplications(ArrayList<String> sentences)
	{
		ArrayList<Implication> allImplications = new ArrayList<Implication>();
		for(int i=0;i<sentences.size();i++)
		{
			if(sentences.get(i).contains("=>"))
			{
				Implication tempImplication = implicationSetup(sentences.get(i));
				allImplications.add(tempImplication);
			}
		}
		return allImplications;
	}
	
	//Setting up each implication
	Implication implicationSetup(String sentence)
	{
		int indexOfImpliesOperator = sentence.indexOf("=");
		
		String  implicationsPredicates = sentence.substring(0,indexOfImpliesOperator);
		String conclusion = sentence.substring(indexOfImpliesOperator+2);	
		
		ArrayList<String> predicates = new ArrayList<String>();
		if(implicationsPredicates.contains("&"))
		{
			String allPredicates[] = implicationsPredicates.split("&");
			for(String predicate:allPredicates)
				predicates.add(predicate);
		}	
		else
			predicates.add(implicationsPredicates);
		
		ArrayList<Predicate> predicatesList = new ArrayList<Predicate>(); 
		
		for(int i=0; i<predicates.size();i++)
		{
			Predicate tempPredicate = new Predicate(predicates.get(i));
			predicatesList.add(tempPredicate);
		}
		Implication tempImplication = new Implication(predicatesList,conclusion);
		return tempImplication;
		
	}
	
	//initializing the facts and implementations
	ArrayList<Fact> initializeFacts(ArrayList<String> sentences)
	{
		ArrayList<Fact> allFacts = new ArrayList<Fact>();
		for(int i=0;i<sentences.size();i++)
		{
			if(!sentences.get(i).contains("=>"))
			{
				Fact fact = new Fact(sentences.get(i));
				allFacts.add(fact);
			}
		}
		return allFacts;
	}
	
	//Backward chaining algorithm
	boolean backwardChaining()
	{
		toCheckPredicateList.add(this.askQuery);
		while(!this.toCheckPredicateList.isEmpty())
		{
			Predicate tempP = toCheckPredicateList.remove(toCheckPredicateList.size()-1);
			traversed.add(tempP);
			if(!checkIsFact(tempP))
			{
				ArrayList<Predicate> premises = new ArrayList<Predicate>();
				for(int i = 0;i<this.allImplications.size();i++)
				{
					if(matchConclusionOfImplications(allImplications.get(i), tempP))
					{
						ArrayList<Predicate> temp = new ArrayList<Predicate>(allImplications.get(i).lhs);
						for(int j=0;j<temp.size();j++)
							premises.add(temp.get(j));						
					}
				}
				if(premises.size() == 0)
				{
					return false;
				}
				else
				{
					for(int i=0; i<premises.size();i++)
					{
						if(!traversed.contains(premises.get(i)))
							toCheckPredicateList.add(premises.get(i));
								
					}
				}
			}
			
			
				
		}
		return true;
	}
	
	boolean checkPredicatesUnified(ArrayList<Predicate> lhs)
	{
		for(Predicate predicate:lhs)
		{
			if(predicate.completeQuery.contentEquals("x"))
				return true;
		}
		return false;
	}
	
	
	boolean matchConclusionOfImplications(Implication implication, Predicate toCheckPredicate)
	{
		Predicate conclusion = new Predicate(implication.rhs);
		
		//conclusion = unifyPredicate(conclusion);
		//toCheckPredicate = unifyPredicate(toCheckPredicate);
		boolean match = matchPredicates(conclusion, toCheckPredicate);
		return match;
	}
	
	//Check if the predicate given is part of the facts
	boolean checkIsFact(Predicate toCheckPredicate)
	{
		boolean contains = false;
		//toCheckPredicate = this.unifyPredicate(toCheckPredicate);
		for(int i=0;i<this.allFacts.size();i++)
		{
			Predicate tempPredicate = this.allFacts.get(i).rhs;
			if(toCheckPredicate.predicate.compareTo(tempPredicate.predicate) == 0)
			{
				if(((toCheckPredicate.argument2 == null && tempPredicate.argument2 == null) || (toCheckPredicate.argument2.compareTo(tempPredicate.argument2)==0)))
					if(toCheckPredicate.argument1.equals("x"))
						contains = true;
					else if(toCheckPredicate.argument1.equals(tempPredicate.argument1))
						contains = true;
			}
			if(true == contains)
			{
				return contains;
			}
		}
		return contains;
	}
	
	//Unifying a given predicate
	Predicate unifyPredicate(Predicate toCheckPredicate)
	{
		Predicate tempP = new Predicate(toCheckPredicate);
		if(tempP.argument1.equals("x"))
		{
			tempP.argument1 = this.askQuery.argument1;
		}
		
		if(tempP.argument2!=null)
		{
			if(tempP.argument2.equals("x"))
			{
				tempP.argument2 = this.askQuery.argument2;
			}
		}	
		
		tempP.completeQuery = replaceXInQuery(tempP);
		return tempP;
	}
	
	//Actual matching of 2 facts
	boolean matchPredicates(Predicate tempPredicate, Predicate toCheckPredicate)
	{
		boolean contains = false;
/*		if(tempPredicate.completeQuery.equals(toCheckPredicate.completeQuery))
			return true;
		else
			return false;*/
		if(toCheckPredicate.predicate.compareTo(tempPredicate.predicate) == 0)
		{
			if(((toCheckPredicate.argument2 == null && tempPredicate.argument2 == null) || (toCheckPredicate.argument2.compareTo(tempPredicate.argument2)==0)))
				if(toCheckPredicate.argument1.equals("x")||tempPredicate.argument1.equals("x"))
					contains = true;
				else if(toCheckPredicate.argument1.equals(tempPredicate.argument1))
					contains = true;
		}
		return contains;
	}
	
	String replaceXInQuery(Predicate tempP)
	{
		if(null != tempP.argument2)
		{
			tempP.completeQuery = replaceXWith2Arguments(tempP.completeQuery);
		}
		else
		{
			tempP.completeQuery = replaceXWith1Argument(tempP.completeQuery);
		}
		return tempP.completeQuery;	
	}
	
	String replaceXWith2Arguments(String completeQuery)
	{
		int indexOfx = completeQuery.indexOf('x');
		int indexOfComma = completeQuery.indexOf(',');
		StringBuilder tempCompleteQuery = new StringBuilder(completeQuery);
		
		if(indexOfx>0)
		{
			if(indexOfx < indexOfComma)
			{
				tempCompleteQuery.deleteCharAt(indexOfx);
				tempCompleteQuery.insert(indexOfx, this.askQuery.argument1);
			}
			else
			{
				tempCompleteQuery.deleteCharAt(indexOfx);
				tempCompleteQuery.insert(indexOfx, this.askQuery.argument2);
			}
		}
		return tempCompleteQuery.toString();
	}
	
	String replaceXWith1Argument(String completeQuery)
	{
		int indexOfx = completeQuery.indexOf('x');
		StringBuilder tempCompleteQuery = new StringBuilder(completeQuery);
		if(indexOfx>0)
		{	
			tempCompleteQuery.deleteCharAt(indexOfx);
			tempCompleteQuery.insert(indexOfx, this.askQuery.argument1);
		}	
		return tempCompleteQuery.toString();
		
	}
}

public class agent 
{
	public static void main(String[] args)
	{
		agent myAgent = new agent();
		ArrayList<String> inputData = myAgent.readInput();
		
		//The first string in the input data contains the ask query
		String ask = inputData.remove(0);		
		KnowledgeBase kb = new KnowledgeBase(ask, inputData);
		
		//myAgent.printInputData(kb);
		
		boolean sentenceProved = kb.backwardChaining();
		//System.out.println(sentenceProved);
		myAgent.printOutputToFile(sentenceProved);
		
	}
	
	private void printOutputToFile(boolean b)
	{
		String output = new String();
		if(true == b)
			output = "TRUE";
		else
			output = "FALSE";
		
		try {
			//setting up the output file
		    File file = new File("output.txt");
            FileWriter fw = new FileWriter(file.getAbsoluteFile());
            BufferedWriter bw = new BufferedWriter(fw);
            
			bw.write(output);		
			//close the file
			bw.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			System.out.println("output.txt was not created due to some reason");
			e.printStackTrace();
		}
		
		catch(IOException ex)
		{
			ex.printStackTrace();
			System.out.println("An IO exception occured");
		}
	}
	
	private void printInputData(KnowledgeBase kb)
	{
		System.out.println("ASKED QUERY:");
		System.out.println(kb.askQuery.completeQuery);
		
		System.out.println("\nFACTS");
		for(int i =0;i<kb.allFacts.size();i++)
		{
			System.out.println(kb.allFacts.get(i).rhs.completeQuery);
		}
		
		System.out.println("\nIMPLICATIONS");
		for(int i=0;i<kb.allImplications.size();i++)
		{
			for(int j=0;j<kb.allImplications.get(i).lhs.size();j++)
			{
				System.out.print(kb.allImplications.get(i).lhs.get(j).completeQuery+"&");
			}
			System.out.print(kb.allImplications.get(i).rhs.completeQuery);
			System.out.println();
		}
	}
	
	private ArrayList<String> readInput()
	{
		ArrayList<String> inputData = new ArrayList<String>();
		
		try
		{
			BufferedReader reader = new BufferedReader(new FileReader("input.txt"));
			
			//Add the query to the inputData[0] and the rest of the 'tell' sentences are appended to the same array
			String ask = reader.readLine();
			inputData.add(ask);
			
			//scan the number of input clauses available in the file
			int numberOfClauses = Integer.parseInt(reader.readLine());
			
			for(int i=0; i < numberOfClauses; i++)
			{
				inputData.add(reader.readLine());
			}
		}
		
		
		catch(FileNotFoundException ex)
		{
			System.out.println(ex.getMessage());
		}
		catch(IOException ex)
		{
			System.out.println(ex.getMessage());
		}
		catch(Exception ex)
		{
			System.out.println(ex.getMessage());
		}		
		return inputData;
	}

}
