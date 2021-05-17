import {
  Component,
  ElementRef,
  Renderer2,
  OnInit,
  ViewChild
} from '@angular/core';
import {Recipe} from "../bakery.api";
import {BakeryService} from "../bakery.service";
import {graphviz}  from 'd3-graphviz';
import {MatSelectionListChange} from "@angular/material/list";
import {AppSettingsService} from "../app.settings";

/** @title Bakery DashboardComponent */
@Component({
  selector: 'dashboard',
  templateUrl: 'home.component.html',
  styleUrls: ['home.css'],
})
export class HomeComponent implements OnInit {

  bakeryVersion: string;
  stateVersion: string;

  constructor(private bakeryService: BakeryService, private renderer:Renderer2)  { }

  ngOnInit(): void {
    this.bakeryVersion = AppSettingsService.settings.bakeryVersion;
    this.stateVersion = AppSettingsService.settings.stateVersion;
  }

}
