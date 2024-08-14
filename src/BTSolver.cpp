#include"BTSolver.hpp"

using namespace std;

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh; 
	cChecks =  cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck ( void )
{
	for ( Constraint c : network.getConstraints() )
		if ( ! c.isConsistent() )
			return false;

	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
    vector<Variable*> toAssign;
    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (int i = 0; i < RMC.size(); ++i)
    {
        vector<Variable*> LV = RMC[i]->vars;
        for (int j = 0; j < LV.size(); ++j)
        {
            if(LV[j]->isAssigned())
            {
                vector<Variable*> Neighbors = network.getNeighborsOfVariable(LV[j]);
                int assignedValue = LV[j]->getAssignment();
                for (int k = 0; k < Neighbors.size(); ++k)
                {
                    Domain D = Neighbors[k]->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return false;
                        if (D.size() == 2)
                            toAssign.push_back(Neighbors[k]);
                        trail->push(Neighbors[k]);
                        Neighbors[k]->removeValueFromDomain(assignedValue);
                    }
                }
            }
        }
    }
    if (!toAssign.empty())
    {
        for (int i = 0; i < toAssign.size(); ++i)
        {
            Domain D = toAssign[i]->getDomain();
            vector<int> assign = D.getValues();
            trail->push(toAssign[i]);
            toAssign[i]->assignValue(assign[0]);
        }
        return arcConsistency();
    }
    return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
 * 		   The bool is true if assignment is consistent, false otherwise.
 */

pair<map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
	map<Variable*, Domain> m; 
    
    //if the given network is not consistent, then return false with an emtpy map.
    if (!network.isConsistent())
         return make_pair(m, false); 
    
    for (auto i : network.getVariables())
    {
        i->getDomain().setModified(false);//set defult modified to false
        
        
        //if the current cell does not have any legal value, then return false with an empty map.
        if(i->getDomain().size() == 0)
            return make_pair(m, false);
        
        if(!i->isAssigned()) //if the current cell (variable) is not assigned, skip.
            continue;
        
        int curVal = i->getAssignment();
            
        for (auto j : network.getNeighborsOfVariable(i)) 
        {
            
            //check neighbor domain to see if the current assigned value exist
            if (j->getDomain().contains(curVal))
            {
                trail->push(j);//push previous variable before deleting 
                j->getDomain().setModified(true);
                j->removeValueFromDomain(curVal);//since conflict with current assigned value, remove it from domain.
                
            }
            
        }
    }
        
    //alternative (for map<Variable*, Domain> m; )
    for(auto i : network.getVariables())
	{
		if(i->getDomain().isModified()) //when it is modified, add i to the output map
		{
			m.insert ( pair<Variable*, Domain>(i, i->getDomain()));
		}
	}
    
    return make_pair(m, network.isConsistent());
}


/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *         The bool is true if assignment is consistent, false otherwise.
 */


/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *         The bool is true if assignment is consistent, false otherwise.
 */

pair<map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
    map<Variable*, int> m;
    //if the given network is not consistent, then return false with an emtpy map.
    if (!network.isConsistent())
         return make_pair(m, false); 
    
    for (auto i : network.getVariables())
    {
        i->getDomain().setModified(false);//set defult modified to false
        
        
        //if the current cell does not have any legal value, then return false with an empty map.
        if(i->getDomain().size() == 0)
            return make_pair(m, false);
        
        if(!i->isAssigned()) //if the current cell (variable) is not assigned, skip.
            continue;
        
        int curVal = i->getAssignment();
            
        for (auto j : network.getNeighborsOfVariable(i)) 
        {
            
            //check neighbor domain to see if the current assigned value exist
            if (j->getDomain().contains(curVal))
            {
                trail->push(j);//push previous variable before deleting 
                j->getDomain().setModified(true);
                j->removeValueFromDomain(curVal);//since conflict with current assigned value, remove it from domain.
                 //probably becasue the above statement only check one time for e???
            //if the current cell does not have any legal value, then return false with an empty map.
                if(j->getDomain().size() == 0)
                    return make_pair(m, false);
            }
            
        }
    }
        
    vector<int> counter;
    for(int c = 0; c <= sudokuGrid.get_n(); c++) //for counting 1-9 only.
            counter.push_back(0);
   //cout << "\n=================================================\n";
    for(auto i: network.getConstraints())
    {
        
        for(int c = 1; c <= sudokuGrid.get_n(); c++) //for counting 1-9 only.
            counter[c] = 0;
        
        for(auto j: i.vars)
        {
            for(auto z: j->getDomain().getValues())
                 counter[z]++; 
        }
        
        vector<int> assign; 
        for(int z = 1; z < counter.size(); z++)
            if(counter[z] == 0)
                return make_pair(m,  false);
            else if(counter[z] == 1)
            {
                for(auto j: i.vars)
                {
                    if(!j->isAssigned() && j->getDomain().contains(z))
                    {
                        m.insert (pair<Variable*, int>(j, z));
                        j->assignValue(z);
                        forwardChecking();
                    }
                }
            }

    }
   
    return make_pair(m,  forwardChecking().second);
}


/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
	return false;
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
     int mrvNum= 9999; // current fewest legal values. The initial number should be infinity. (e.g. 9999) 
    Variable* mrvPos = nullptr; // current fewest legal variable. The initial number should be nullptr. 
    for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) ) //if current variable is assigned, skip.
            if(mrvNum > v->getDomain().size()) //check whether has a smaller minimum size
            {
                mrvNum = v->getDomain().size(); //assigned minimum size
                mrvPos = v; //records minimum position pointer 
            }
    return mrvPos;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */

/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number 
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
    int mrvNum= 9999; // current fewest legal values. The initial number should be infinity. (e.g. 9999) 
    Variable* mrvPos = nullptr; // current fewest legal variable. The initial number should be nullptr. 
    vector<Variable*> m;//added for MRVwithTieBreaker
    int maxCounter = 0;
    vector<Variable*> candidate;
    for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) ) //if current variable is assigned, skip.
        {
            if(mrvNum > v->getDomain().size()) //check whether has a smaller minimum size
            {
                candidate.clear();
                
                mrvNum = v->getDomain().size(); //assigned minimum size
                mrvPos = v; //records minimum position pointer
                
                int LC = 0; //local counter
                for(auto j: network.getNeighborsOfVariable(v))
                    if(!j->isAssigned())
                        LC++;
                
                 maxCounter = LC;
            }
            else if (mrvNum == v->getDomain().size())
            {
                int LC = 0; //local counter
                for(auto j: network.getNeighborsOfVariable(v))
                    if(!j->isAssigned())
                        LC++;
                if(LC > maxCounter)
                {
                    maxCounter = LC;
                    mrvPos = v;
                    candidate.clear();
                }
                else if(LC == maxCounter)
                    candidate.push_back(v);
            }
        }
    
    //cout << "==================\n";
    
    m.clear();
    m.push_back(mrvPos);//added for MRVwithTieBreaker
    for(auto i : candidate)
        m.push_back(i);
    
    return m;
    
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar ( void )
{
	return nullptr;
}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */
vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
    vector< pair <int,int> > conflictVec; //conflict number of each value.
    
    for(auto i : v->getDomain().getValues()) //i = current value 
    {
        int conflict = 0;// counter for conflict
        for(auto j: network.getNeighborsOfVariable(v)) //j = current neighbor 
            if(j->getDomain().contains(i)) // whether j's domain contain current value
                conflict++; //counter increment 
        conflictVec.push_back( make_pair(conflict, i) ); //add it to pair vector 
    }
    
    sort(conflictVec.begin(), conflictVec.end()); //sort the vector by conflictVec.first (conflicts) in ascending order
    vector<int> sortList;//result vector
    for (auto it = conflictVec.begin(); it != conflictVec.end(); ++it)
        sortList.push_back(it->second); //convert pairs.second to sortlist
    
     return sortList;
}

/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
	return vector<int>();
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
    clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );

		// Assign the value
		v->assignValue( i );

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}
			
		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();

	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
		return MRVwithTieBreaker()[0];

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}
