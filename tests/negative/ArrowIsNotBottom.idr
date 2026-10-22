module ArrowIsNotBottom
import PLFA.Part3.Denotational
%default total
bad : Info (Arrow Bottom Bottom) Bottom
bad = IBot
