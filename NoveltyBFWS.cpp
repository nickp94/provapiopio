/* (C) Copyright 2002  Universita' degli Studi di Brescia
 *     Dipartimento di Elettronica per l'Automazione
 *     Via Branze 38, 25123 Brescia, Italy
 *
 * All rights reserved. Use of this software is permitted ONLY for
 * non-commercial research purposes, and it may be copied only
 * for that use only. All copies must include this copyright message.
 * This software is made available AS IS, and neither the authors
 * nor the University of Brescia make any warranty about the
 * software or its performance.
 *
 *********************************************************************/



/********************************************************************
 * File: noveltyBFWS.cpp
 * Description: Define and update the novelty for BFWS
 * NOTE : we are considering Max arity=2 !!!!!!
 *
 *   PDDL 2.1 version without conditional and quantified effects
 *
 * Authors: Ivan Serina
 *
 *********************************************************************/


#ifdef __IW__
#include "NoveltyBFWS.h"
#include <iostream>
#include <queue>

using namespace std;

//Struttura dati utilizzata per f5, salva le tuple in varie multimap, ogni multimap corrisponde ad valore dato da #r*num_goal+#g
//in modo da avere un indice
void NoveltyBFWS::my_or(int* bit_array1,int* bit_array2,int len)
{
	for(int i=0;i<len;i++)
	{
		bit_array1[i] |= bit_array2[i];
	}
}
void my_print_array(int* bit_array,int len)
{
	cout << "PRINT ARRAYYYYYYYYYYYYYYY!!!!!" << endl;
	//printf("\nMissing fact %d, novelty =1", facts[i]);
	for(int i=0;i<len;i++)
	{
		cout << bit_array[i] << "--";
	}
	cout << endl;
	cout << "END ARRAYYYYYYYYYYYYYYY!!!!!" << endl;
}
NoveltyBFWS::NoveltyBFWS(int new_max_arity)
{
  if(new_max_arity>2){
    fprintf(stderr,"\nMax arity value = 2; forced it");
    new_max_arity=2;
  }
  max_arity= new_max_arity;
  max_bfws_g=1;
  max_bfws_r=1;
}

NoveltyBFWS::~NoveltyBFWS() // DA FARE!!!!!
{
	// TODO Auto-generated destructor stub
	index_mutex_map.novelty_table_arity1.clear();

	map<long int, map<int, int*>>::iterator long_iterator=novelty_table_arity2.begin();
	while(long_iterator != novelty_table_arity2.end())
	{
		map<int, int*> &supported_facts_map= long_iterator->second;
		map<int, int*>::iterator delete_iterator=supported_facts_map.begin();
		while(delete_iterator != supported_facts_map.end())
		{
			//int* array_da_cancellare=delete_iterator->second;
			//free(array_da_cancellare);
			free(delete_iterator->second);
			delete_iterator++;
		}
		long_iterator++;
	}
	index_mutex_map.novelty_table_arity2.clear();
	index_mutex_map.novelty_table_arity2_E1.clear(); //+++
}


//Calcola un unico valore euristico che incorpora i due
long int NoveltyBFWS::get_index_state(int g, int r )
{
  return r+g*max_bfws_r;
}

int NoveltyBFWS::compute_novelty( BfsNode* bfs_node )
{
	// Starting initializations
	int novelty = this->max_arity+1;
	int ef=bfs_node->op;
	int * facts;
	int num_facts;
	static int num_compute_novelty=0;
	if(max_bfws_g < bfs_node->bfws_g)
	{
		max_bfws_g = bfs_node->bfws_g;
	}
	if(max_bfws_r < bfs_node->bfws_r)
	{
		max_bfws_r = bfs_node->bfws_r;
	}
	long int index_state=get_index_state( bfs_node->bfws_g, bfs_node->bfws_r);
	// Check for arity 1
	if(DEBUG2)
	{
		printf("\nNovelty check %d for index: %ld, act %d", ++num_compute_novelty, index_state, ef);
	}


	// check if present the structure for the current index_state, if not novelty<-1
	mutex_map.lock();
	map<long int,full_arity>::iterator full_arity_it = full_novelty_table_arity_map.find(index_state);
	mutex_map.unlock();

	if(full_arity_it==full_novelty_table_arity_map.end())// se è vuota la mappa....
	{
		//New set
		if(DEBUG3)
		{
			printf("\nMissing fact set for index:  %ld, novelty =1", index_state);
		}
		novelty = 1;
		return novelty;
	}


	// structure containing the maps and set
	full_arity &current_arity_struct=full_arity_it->second;


	// Check for NOVELTY 1
	const set<int> &supported_facts= current_arity_struct.novelty_table_arity1;

	if(bfs_node->father && bfs_node->father->index_state==index_state && ef>=0)
	{// check only the additive effects of the applied action
		facts=gef_conn[ef].A;
		num_facts=gef_conn[ef].num_A;
	}
	else
	{// check all the facts (compressed and not) in the state
		facts=bfs_node->S.F;
		num_facts=bfs_node->S.num_F;
#ifndef __C1__
		if(bfs_node->S.num_C1_F>0 && DEBUG2)
		{
			printf("\nWarning bfs_node->S.num_C1_F shoudl be = to 0 ");
			exit(1);
		}
#endif
		// check for compressed facts
		if(bfs_node->S.num_C1_F>0)
		{
			for(int i=0; i<bfs_node->S.num_C1_F; i++)
			{
				current_arity_struct.mutex_nov1.lock();
				if(supported_facts.find(bfs_node->S.C1_F[i])==supported_facts.end())
				{
					if(DEBUG3)
					{
						printf("\nMissing fact %d, novelty =1", bfs_node->S.C1_F[i]);
					}
					current_arity_struct.mutex_nov1.unlock();
					novelty = 1;
					return novelty;
				}
				current_arity_struct.mutex_nov1.unlock();
			}
		}
		// Continue the check for the other values
	}
	for(int i=0; i<num_facts; i++)
	{
		current_arity_struct.mutex_nov1.lock();
		if(supported_facts.find(facts[i])==supported_facts.end())
		{
			current_arity_struct.mutex_nov1.unlock();
			if(DEBUG3)
			{
				printf("\nMissing fact %d, novelty =1", facts[i]);
			}
			novelty = 1;
			return novelty;
		}
		current_arity_struct.mutex_nov1.unlock();
	}



	// Check for NOVELTY 2
	map<int, int*> &supported_facts_map= current_arity_struct.novelty_table_arity2;
	map<int, set<int>> &supported_facts_map_E1= current_arity_struct.novelty_table_arity2_E1;

	// Starting initialization of structures
	facts=bfs_node->S.F;
	num_facts=bfs_node->S.num_F;
	//set<int>supported_facts_set; //
	set<int,greater<int>> supported_facts_set;// decrescente, in realtà non serve
	for(int i=0; i< num_facts; i++)
	{
		supported_facts_set.insert(facts[i]);
	}
	// check for E1
	if(bfs_node->S.num_C1_F>0)
	{
		for(int i=0; i<bfs_node->S.num_C1_F; i++)
		{
			supported_facts_set.insert(bfs_node->S.C1_F[i]);
		}
	}

	// check novelty 2
	if(bfs_node->father && bfs_node->father->index_state==index_state && ef>=0)
	{// check only the additive effects of the applied action
		facts=gef_conn[ef].A;
		num_facts=gef_conn[ef].num_A;

		for(int i=0; i<num_facts; i++)
		{
			int fact=facts[i];

			//map<int,bitset<gnum_ft_conn>*>::iterator sf_it= supported_facts_map.find(fact);
			current_arity_struct.mutex_nov2_barray.lock();
			map<int,int*>::iterator sf_it= supported_facts_map.find(fact);
			current_arity_struct.mutex_nov2_barray.unlock();
			current_arity_struct.mutex_nov2_E1.lock();
			map<int,set<int>>::iterator sf_it_E1= supported_facts_map_E1.find(fact);
			current_arity_struct.mutex_nov2_E1.unlock();

			if(sf_it== supported_facts_map.end() && sf_it_E1== supported_facts_map_E1.end())
			{
				// non può succedere, novelty 1
				if(DEBUG3)
				{
					printf("\nWhy is not novelty=1 in fact: %d ?", fact);
				}
				novelty = 2;
				return novelty;
			}
			else
			{
				for(auto fact2 : supported_facts_set )
				{
					if(fact2<fact)
					{
						if(fact2<gnum_ft_conn)
						{
							if(sf_it== supported_facts_map.end())
							{
								// found a new couple
								novelty=2;
								return novelty;
							}
							else
							{
								if(!GET_BIT(sf_it->second,fact2))
								{
									// found a new couple
									novelty=2;
									return novelty;
								}
							}
						}
						else
						{
							if(sf_it_E1== supported_facts_map_E1.end())
							{
								novelty=2;
								return novelty;
							}
							else
							{
								const set<int> &second_supported_facts_set=sf_it_E1->second;
								current_arity_struct.mutex_nov2_E1.lock();
								if(second_supported_facts_set.find(fact2)==second_supported_facts_set.end())
								{
									// found a new couple
									novelty=2;
									return novelty;
								}
								current_arity_struct.mutex_nov2_E1.unlock();
							}
						}
					}
				}
			}
		}
		for(auto fact : supported_facts_set ) // all facts in the state
		{
			current_arity_struct.mutex_nov2_barray.lock();
			map<int,int*>::iterator sf_it= supported_facts_map.find(fact);
			current_arity_struct.mutex_nov2_barray.unlock();

			if(sf_it== supported_facts_map.end())
			{
				// found a new couple
				novelty=2;
				return novelty;
			}
			else
			{
				for(int i=0; i<num_facts; i++) // only additive effects, that will be < gnum_ft_conn, so i check only bitarray
				{
					int fact2=facts[i];
					if(fact2<fact)
					{
						if(fact2<gnum_ft_conn)
						{
							if(!GET_BIT(sf_it->second,fact2))
							{
								// found a new couple
								novelty=2;
								return novelty;
							}
						}
						else
						{
							// print error
						}
					}
				}
			}
		}
	}
	else // ef<0 // sono arrivato qui
	{
		for(auto fact : supported_facts_set )
		{
			full_novelty_table_arity_map.mutex_nov2_barray.lock();
			map<int,int*>::iterator sf_it= supported_facts_map.find(fact);
			full_novelty_table_arity_map.mutex_nov2_barray.unlock();
			full_novelty_table_arity_map.mutex_nov2_E1.lock();
			map<int,set<int>>::iterator sf_it_E1= supported_facts_map_E1.find(fact);
			full_novelty_table_arity_map.mutex_nov2_E1.unlock();

			if(sf_it_E1== supported_facts_map_E1.end() && sf_it== supported_facts_map.end())
			{
				// Questo controllo deve essere loccato???
				novelty = 2;
				return novelty;
			}
			else
			{
				for(auto fact2 : supported_facts_set )
				{
					if(fact2<fact)
					{
						if(fact2<gnum_ft_conn)
						{
							// nel bitset non serve il lock
							if(sf_it== supported_facts_map.end())
							{
								novelty=2;
								return novelty;
							}
							// guardo in arity2, bitset
							else
							{
								//if(!sf_it->second->test(fact2))
								if(!GET_BIT(sf_it->second,fact2))
								{
									// found a new couple
									novelty=2;
									return novelty;
								}
							}
						}
						else
						{
							if(sf_it_E1== supported_facts_map_E1.end())
							{
								// found a new couple
								novelty=2;
								return novelty;
							}
							else
							{
								const set<int> &second_supported_facts_set=sf_it_E1->second;
								// guardo in arity2_E1
								current_arity_struct.mutex_nov2_E1.lock();
								if(second_supported_facts_set.find(fact2)==second_supported_facts_set.end())
								{
									// found a new couple
									current_arity_struct.mutex_nov2_E1.unlock();
									novelty=2;
									return novelty;
								}
								current_arity_struct.mutex_nov2_E1.unlock();
							}
						}
					}
				}
			}
		}
	}
	return novelty;
}


bool NoveltyBFWS::update_novelty( BfsNode* bfs_node )
{
	int ef=bfs_node->op;
	int * facts;
	int num_facts;
	static int num_update_novelty=0;
	long int index_state=get_index_state( bfs_node->bfws_g, bfs_node->bfws_r);
	if(DEBUG2)
	printf("\nNovelty update %d for index: %ld", ++num_update_novelty, index_state);


	mutex_map.lock();
	map<long int,full_arity>::iterator full_arity_it = full_novelty_table_arity_map.find(index_state);
	mutex_map.unlock();

	if(full_arity_it==full_novelty_table_arity_map.end())// se è vuota la mappa....
	{
		full_arity new_arity_struct;

		mutex_map.lock();
		full_novelty_table_arity_map.insert(make_pair(index_state,new_arity_struct));
		map<long int,full_arity>::iterator full_arity_it = full_novelty_table_arity_map.find(index_state);
		mutex_map.unlock();
	}
	full_arity &current_arity_struct=full_arity_it->second;



	// update Novelty 1
	set<int> &supported_facts= current_arity_struct.novelty_table_arity1;
	if(bfs_node->father && bfs_node->father->index_state==index_state && ef>=0)// check only the additive effects of the applied action
	{
		facts=gef_conn[ef].A;
		num_facts=gef_conn[ef].num_A;
	}
	else
	{
		facts=bfs_node->S.F;
		num_facts=bfs_node->S.num_F;

		// check for E2
		if(bfs_node->S.num_C1_F>0)
		{
			current_arity_struct.mutex_nov1.lock();
			for(int i=0; i<bfs_node->S.num_C1_F; i++)
			{
				supported_facts.insert(bfs_node->S.C1_F[i]);
			}
			current_arity_struct.mutex_nov1.unlock();
		}
	}
	current_arity_struct.mutex_nov1.lock();
	for(int i=0; i< num_facts; i++)
	{
		if(DEBUG3)
		{
			printf("\nInsert fact %d for index:  %ld", facts[i], index_state);
		}
		supported_facts.insert(facts[i]);
	}
	current_arity_struct.mutex_nov1.unlock();



	// NOVELTTY 2   TODO Check
	facts=bfs_node->S.F;
	num_facts=bfs_node->S.num_F;


	// initialization of struct that represent current State
	// all_supported_facts_set-> is the set of all the facts, compressed and not
	// compressed_supported_facts_set -> is the set of all compressed facts
	// supported_facts_bitset -> bit_array where are set=1 only the bits corresponding to non compressed facts of this State
	int* supported_facts_bitset;// devo inizializzarlo a zero???
	int size_bitarray=(gnum_ft_conn/32)+1;
	//supported_facts_bitset = (int*) calloc(size_bitarray, sizeof(int));
	supported_facts_bitset = alloc_vect(size_bitarray);
	set<int>compressed_supported_facts_set;
	set<int>all_supported_facts_set;

	for(int i=0; i< num_facts; i++)
	{
		all_supported_facts_set.insert(facts[i]);
		if(facts[i]<gnum_ft_conn)
		{
			//supported_facts_bitset.set(facts[i]);
			SET_BIT(supported_facts_bitset,facts[i]);
		}
		else
		{
			compressed_supported_facts_set.insert(facts[i]);
		}
	}
	// check for E1
	if(bfs_node->S.num_C1_F>0)
	{
		for(int i=0; i<bfs_node->S.num_C1_F; i++)
		{
			all_supported_facts_set.insert(bfs_node->S.C1_F[i]);
			if(bfs_node->S.C1_F[i]<gnum_ft_conn)
			{
				// non dovrebbe succedere
				SET_BIT(supported_facts_bitset,bfs_node->S.C1_F[i]);
				if(DEBUG3)
				{
					printf("\nError, this fact: %d  is not of E1 for index: %ld", facts[i], index_state);
				}
			}
			else
			{
				compressed_supported_facts_set.insert(bfs_node->S.C1_F[i]);
			}
		}
	}

	// AGGIORNO: novelty_table_arity2 (BITARRAY)
	map<int,int*> &supported_facts_map= current_arity_struct.novelty_table_arity2;
	// ottimizzazione
	if(bfs_node->father && bfs_node->father->index_state==index_state && ef>=0)// check only the additive effects of the applied action
	{
		facts=gef_conn[ef].A;
		num_facts=gef_conn[ef].num_A;

		int* second_supported_facts_bitset;
		//second_supported_facts_bitset= (int*) calloc(size_bitarray, sizeof(int));
		second_supported_facts_bitset= alloc_vect(size_bitarray);

		for(int i=0; i< num_facts; i++)
		{
			if(facts[i]<gnum_ft_conn)
			{
				//second_supported_facts_bitset.set(facts[i]);
				SET_BIT(second_supported_facts_bitset,facts[i]);
			}
		}

		// First add the  supported facts to the additive effects
		for(int i=0; i< num_facts; i++)
		{
			int fact=facts[i];

			//map<int,bitset<gnum_ft_conn>*>::iterator sf_it= supported_facts_map.find(fact);
			current_arity_struct.mutex_nov2_barray.lock();
			map<int,int*>::iterator sf_it= supported_facts_map.find(fact);
			if(sf_it== supported_facts_map.end())
			{
				int* bit_array_da_inserire;
				//bit_array_da_inserire = (int*) calloc(size_bitarray, sizeof(int));
				bit_array_da_inserire = alloc_vect(size_bitarray);
				my_or(bit_array_da_inserire,supported_facts_bitset,size_bitarray);
				supported_facts_map.insert(make_pair(fact,bit_array_da_inserire));
			}
			else
			{
				my_or(sf_it->second,supported_facts_bitset,size_bitarray);
			}
			current_arity_struct.mutex_nov2_barray.unlock();
		}
		//Then add the additive effects to the  supported facts
		for(auto fact : all_supported_facts_set )
		{
			//map<int,bitset<gnum_ft_conn>*>::iterator sf_it= supported_facts_map.find(fact);
			current_arity_struct.mutex_nov2_barray.lock();
			map<int,int*>::iterator sf_it= supported_facts_map.find(fact);
			if(sf_it== supported_facts_map.end())// forse questo si può evitare di fare
			{
				int* bit_array_da_inserire;
				bit_array_da_inserire = (int*) calloc(size_bitarray, sizeof(int));
				my_or(bit_array_da_inserire,second_supported_facts_bitset,size_bitarray);
				supported_facts_map.insert(make_pair(fact,bit_array_da_inserire));
			}
			else
			{
				my_or(sf_it->second,second_supported_facts_bitset,size_bitarray);
			}
			current_arity_struct.mutex_nov2_barray.unlock();
		}
	}
	else
	{
		//Add all the couple of facts: one element and all the others
		for(auto fact : all_supported_facts_set )
		{
			//map<int,bitset<gnum_ft_conn>*>::iterator sf_it= supported_facts_map.find(fact);
			current_arity_struct.mutex_nov2_barray.lock();
			map<int,int*>::iterator sf_it= supported_facts_map.find(fact);
			if(sf_it== supported_facts_map.end())
			{
				int* bit_array_da_inserire;
				bit_array_da_inserire = (int*) calloc(size_bitarray, sizeof(int));
				my_or(bit_array_da_inserire,supported_facts_bitset,size_bitarray);
				supported_facts_map.insert(make_pair(fact,bit_array_da_inserire));
			}
			else
			{
				my_or(sf_it->second,supported_facts_bitset,size_bitarray);
			}
			current_arity_struct.mutex_nov2_barray.unlock();
		}
	}



	// AGGIORNO: novelty_table_arity2_E1 (SET)
	map<int, set<int>> &supported_facts_map_E1= current_arity_struct.novelty_table_arity2_E1;
	//Add all the couple of facts: one element and all the others
	for(auto fact : compressed_supported_facts_set )
	{
		current_arity_struct.mutex_nov2_barray.lock();
		map<int,set<int>>::iterator sf_it_E1= supported_facts_map_E1.find(fact);
		if(sf_it_E1== supported_facts_map_E1.end())
		{
			supported_facts_map_E1.insert(make_pair(fact,compressed_supported_facts_set));
		}
		else
		{
			sf_it_E1->second.insert(compressed_supported_facts_set.begin(),compressed_supported_facts_set.end());
		}
		current_arity_struct.mutex_nov2_barray.unlock();
	}
}
#endif
