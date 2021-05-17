import {
  Component,
  ElementRef,
  Renderer2,
  OnInit,
  ViewChild
} from '@angular/core';
import {Interaction, Recipe} from "../bakery.api";
import {BakeryService} from "../bakery.service";
import {graphviz}  from 'd3-graphviz';
import {MatSelectionListChange} from "@angular/material/list";

/** @title Bakery DashboardComponent */
@Component({
  selector: 'dashboard',
  templateUrl: 'interactions.component.html',
  styleUrls: ['interactions.css'],
})
export class InteractionsComponent implements OnInit {
  interactions: Interaction[];
  selectedInteraction: Interaction;

  selectedInteractionInput(): string {
    return JSON.stringify(this.selectedInteraction?.input, null, 4);
  }

  selectedInteractionOutput(): string {
    return JSON.stringify(this.selectedInteraction?.output, null, 4);
  }

  @ViewChild('interactionView', { static: false }) interactionView: ElementRef;

  constructor(private top: ElementRef,
              private bakeryService: BakeryService, private renderer:Renderer2)  { }

  ngOnInit(): void {
    this.getInteractions();
  }

  getInteractions(): void {
    this.bakeryService.getInteractions().subscribe( interactions =>
      this.interactions = interactions.sort((a, b) => a.name.localeCompare(b.name)));
  }

  interactionChanged(event: MatSelectionListChange): void {
    let interaction = <Interaction> event.options[0].value;
    this.selectedInteraction = interaction;
  }
}

