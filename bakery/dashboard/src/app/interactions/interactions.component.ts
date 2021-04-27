import {MediaMatcher} from '@angular/cdk/layout';
import {ChangeDetectorRef, Component, OnDestroy, OnInit} from '@angular/core';
import {Interaction, Recipe} from "../bakery-api";
import {BakeryService} from "../bakery.service";

/** @title Bakery DashboardComponent */
@Component({
  selector: 'dashboard',
  templateUrl: 'interactions.component.html',
  styleUrls: ['interactions.css'],
})

export class InteractionsComponent implements OnInit {
  interactions: Interaction[];

  constructor(private bakeryService: BakeryService) { }

  ngOnInit(): void {
    this.getInteractions();
  }

  getInteractions(): void {
    this.bakeryService.getInteractions().subscribe( interactions => this.interactions = interactions);
  }


}
