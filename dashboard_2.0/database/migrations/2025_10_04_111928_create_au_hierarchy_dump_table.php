<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::create('au_hierarchy_dump', function (Blueprint $table) {
            $table->id();
            $table->string('designation', 255);
            $table->string('job_id', 100);
            $table->string('job_family', 200)->nullable();
            $table->string('department_name', 200)->nullable();
            $table->string('department_code', 50)->nullable();
            $table->string('vertical_name', 200)->nullable();
            $table->string('vertical_code', 50)->nullable();
            $table->string('bu', 200)->nullable();
            $table->integer('branch_category_id')->nullable();
            $table->string('misid', 50)->nullable();
            $table->string('role_id', 50)->nullable();
            $table->string('report_role_type', 100)->nullable();
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('au_hierarchy_dump');
    }
};
