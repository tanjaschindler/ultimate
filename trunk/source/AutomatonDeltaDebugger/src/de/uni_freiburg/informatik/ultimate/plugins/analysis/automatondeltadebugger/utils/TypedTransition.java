/*
 * Copyright (C) 2015-2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.utils;

/**
 * Wraps a transition together with its type (internal, call, return).
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class TypedTransition<LETTER, STATE> {
	private final STATE mPred;
	private final STATE mSucc;
	private final STATE mHier;
	private final TypedLetter<LETTER> mLetter;
	
	/**
	 * Constructor.
	 * 
	 * @param pred
	 *            predecessor state
	 * @param succ
	 *            successor state
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            letter
	 */
	public TypedTransition(final STATE pred, final STATE succ, final STATE hier,
			final TypedLetter<LETTER> letter) {
		this.mPred = pred;
		this.mSucc = succ;
		this.mHier = hier;
		this.mLetter = letter;
	}
	
	public STATE getPred() {
		return mPred;
	}
	
	public STATE getSucc() {
		return mSucc;
	}
	
	public STATE getHier() {
		return mHier;
	}
	
	public TypedLetter<LETTER> getLetter() {
		return mLetter;
	}
	
	@Override
	public int hashCode() {
		final int hashCode = (mHier == null) ? 0 : mHier.hashCode();
		return hashCode + mPred.hashCode() + mSucc.hashCode() + mLetter.hashCode();
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(final Object obj) {
		if ((obj == null) || (this.getClass() != obj.getClass())) {
			return false;
		}
		final TypedTransition<LETTER, STATE> other = (TypedTransition<LETTER, STATE>) obj;
		if (this.mHier == null ^ other.mHier == null) {
			return false;
		}
		return (other.mPred.equals(this.mPred)) && (other.mSucc.equals(this.mSucc))
				&& (other.mLetter.equals(this.mLetter));
	}
	
	@Override
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append("<");
		b.append(mPred);
		b.append(", ");
		b.append(mLetter);
		if (mHier != null) {
			b.append(mHier);
			b.append(", ");
		}
		b.append(", ");
		b.append(mSucc);
		b.append(">");
		return b.toString();
	}
}
