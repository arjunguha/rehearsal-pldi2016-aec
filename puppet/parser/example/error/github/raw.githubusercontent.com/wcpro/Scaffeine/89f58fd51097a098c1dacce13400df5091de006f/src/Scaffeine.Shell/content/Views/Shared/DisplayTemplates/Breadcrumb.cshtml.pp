@model $rootnamespace$.Extensions.BreadcrumbHelperModel

<div class="breadcrumb">
    @foreach (var node in Model) { 
    @Html.DisplayFor(m => node);
    
    if (node != Model.Last()) {
        <text> &gt; </text>
    }
}
</div>
