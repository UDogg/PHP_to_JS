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
        if (!Schema::hasTable('usertypes'))
        {
            Schema::Create('usertypes', function (Blueprint $table) {
                $table->id();
                $table->string('name');
                $table->timestamps();
                $table->enum('is_active',['N','Y'])->default('Y');
                $table->softDeletes();
                $table->string('Identifier',10)->nullable();

            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
    }
};
