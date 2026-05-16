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
        Schema::table('misp_branches', function (Blueprint $table) {
            $table->string('zone')->nullable();
            $table->string('mobile_number')->nullable();
            $table->string('email')->nullable();
            $table->enum('status',['Y','N'])->default('Y');
            $table->softDeletes()->after('updated_at');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('misp_branches', function (Blueprint $table) {
            //
        });
    }
};
